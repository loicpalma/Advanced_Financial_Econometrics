%let chemin=C:\YourFolder\YourData;

libname afe "&chemin";
%let path = afe;
%let list = "ABCA,Airbus,BNP,OR,SAN";

%macro import(list);

	data _null_;	
		call symputx('nb',countw(&list,','));
	run;


	%do i=1 %to &nb;	

		data _null_;
			call symputx("infile_name",scan(&list,&i,','));
		run;

		ods exclude all;
		PROC IMPORT OUT=&infile_name.
            DATAFILE= "&chemin\&infile_name..csv"
            DBMS=CSV REPLACE;
     		GETNAMES=YES;
		RUN;


		data Rendement_&infile_name.(keep=date rendement_&infile_name.);
			set &infile_name.;
			rendement_&infile_name. = log(close)-log(lag(close));
			if _n_=1 then delete;
		run;

		/*If we are at the first asset, then we create the table. Otherwise, we add a new column */

		%if &i.=1 %then %do;

			data portfolio;
				set rendement_&infile_name.;
			run;

		%end;

		%else %do;

			data portfolio;
				merge portfolio rendement_&infile_name.;
				by Date;
			run;

		%end;
	%end;
	ods exclude none;
%mend;

%import(&list.);


data actions ; 
	merge ABCA (KEEP=Date Close RENAME=(Close=CloseABCA)) Airbus (KEEP=Date Close RENAME=(Close=CloseAirbus)) BNP (KEEP=Date Close RENAME=(Close=CloseBNP))
				OR (KEEP=Date Close RENAME=(Close=CloseOR)) SAN (KEEP= Date Close RENAME=(Close=CloseSAN));
	by date;
RUN;
proc sgplot data=actions;
	title "Evolution of share prices";
	label Closeabca="ABC Arbitrage" Closeairbus="Airbus" Closebnp="BNP" Closeor="L'Oréal" Closesan="Sanofi";
	series x=date y=Closeabca;
	series x=date y=closeairbus;
	series x=date y=closebnp;
	series x=date y=closeor;
	series x=date y=closesan;
	yaxis display=(nolabel);
quit;

/*We calculate the variances and covariances of our actions using the proc varmax */

proc varmax data=portfolio outest=oedcc outcov noprint;
   model rendement: / noint;
   garch p=1 q=1 form=dcc outht=ohdcc;
run;


%let n=5; 


%macro automatisation();


	proc sql;
		drop table portfolio_mv_strategy;
		drop table portfolio_naive_strategy;
		drop table portfolio_mv_strategy_wcons;
		drop table portfolio_RP_strategy;
		drop table poids_opt_rp;
		drop table poids_opt_mv;
		drop table poids_opt_mv_cont;
	quit;


	%do i=121 %to 1241 %by 20;


		data toto;
			set ohdcc;
			if _n_=&i. then output;
		run;

		data toto;
			retain h1_1 h1_2 h1_3 h1_4 h1_5 
	  			   h2_1 h2_2 h2_3 h2_4 h2_5 
	  			   h3_1 h3_2 h3_3 h3_4 h3_5 
	  			   h4_1 h4_2 h4_3 h4_4 h4_5
	   			   h5_1 h5_2 h5_3 h5_4 h5_5;
			set toto;
			h2_1 = h1_2;
			h3_1 = h1_3;
			h3_2 = h2_3;
			h4_1 = h1_4;
			h4_2 = h2_4;
			h4_3 = h3_4;
			h5_1 = h1_5;
			h5_2 = h2_5;
			h5_3 = h3_5;
			h5_4 = h4_5;
		run;


		data estim_twenty_days;
			set portfolio;
			if &i.< _n_ < &i.+21 then output;
		run;

		PROC IML;

			use estim_twenty_days;
				read all var{rendement_ABCA rendement_Airbus rendement_BNP rendement_OR rendement_SAN}  into rend[colname=varNames];
			close estim_twenty_days;

			omega_naif = {0.2 , 0.2 , 0.2 , 0.2 , 0.2};
			return = rend * omega_naif;

			create return_naif from return;
				append from return;
			close return_naif;

			use toto;
  				read all var _ALL_ into A[colname=varNames]; 
			close toto;

			s= shape(A,5,5);

			e = {1,1,1,1,1};
			s_inv = inv(s);

			h = s_inv * e;

			b = t(e) * s_inv * e;

			omega_mv = h/b;

			return_mv = rend * omega_mv;

			create omega_mv from omega_mv;
				append from omega_mv;
			close omega_mv ; 

			create return_mv from return_mv;
				append from return_mv;
			close return_mv;

			create varcov from s;
				append from s;
			close varcov;

		QUIT;
		/******************************************************************************************************************/
		/* Optimization of portfolio weights with the MV (Minimum Variance) strategy */
		proc optmodel;
			set N = 1..&n.; /* N number of assets index  */
			num var{N,N}; /* N x N covariance matrix   */
			var x{i in N} init 1/&n.; /* N x 1 vector of weights   */
			/* Objective Function */
			min f = (sum{i in N}(sum{j in N}(x[i]*var[i,j]*x[j])));
			/* Constraints */
			con c1: sum{i in N} x[i] = 1;
			con c2: min{i in N} x[i] >= 0;
			/* Reading Data */
			read data varcov into[_n_]{i in N}<var[_n_,i]=col("COL"||i)>;
			/* Execute Optimization */
			solve with ipnlp;
			/* Create Solution Weights Data Set */
			create data min_var_weights from {i in N}<col("x"||i)=x[i]>;
			/* Print Solution Weights */
		quit;

		/******************************************************************************************************************/
		/* Optimization of portfolio weights with the PR strategy (Risk Parity) */

		proc sql noprint; 
			select col1,col2,col3,col4,col5
			into :A1-:A5, :B1-:B5, :C1-:C5, :D1-:D5, :E1-:E5
			from varcov;
		quit;
		proc optmodel;
			var weight{1..5} >= 0;
			num coeff{1..5,1..5} = [&A1. &B1. &C1. &D1. &E1.
									&A2. &B2. &C2. &D2. &E2.
									&A3. &B3. &C3. &D3. &E3.
									&A4. &B4. &C4. &D4. &E4.
									&A5. &B5. &C5. &D5. &E5.];

   			con s1: ((weight[1]*(&A1.*weight[1]+&B1.*weight[2]+&C1.*weight[3]+&D1.*weight[4]+&E1.*weight[5])) /
		   			sum{i in 1..5, j in 1..5}coeff[i,j]*weight[i]*weight[j]) = 0.2;

	    	con s2: ((weight[2]*(&A2.*weight[1]+&B2.*weight[2]+&C2.*weight[3]+&D2.*weight[4]+&E2.*weight[5])) /
		   			sum{i in 1..5, j in 1..5}coeff[i,j]*weight[i]*weight[j]) = 0.2;

 	    	con s3: ((weight[3]*(&A3.*weight[1]+&B3.*weight[2]+&C3.*weight[3]+&D3.*weight[4]+&E3.*weight[5])) /
		   			sum{i in 1..5, j in 1..5}coeff[i,j]*weight[i]*weight[j]) = 0.2;

   			con s4: ((weight[4]*(&A4.*weight[1]+&B4.*weight[2]+&C4.*weight[3]+&D4.*weight[4]+&E4.*weight[5])) /
		   			sum{i in 1..5, j in 1..5}coeff[i,j]*weight[i]*weight[j]) = 0.2;

   			con s5: ((weight[5]*(&A5.*weight[1]+&B5.*weight[2]+&C5.*weight[3]+&D5.*weight[4]+&E5.*weight[5])) /
		   			sum{i in 1..5, j in 1..5}coeff[i,j]*weight[i]*weight[j]) = 0.2;

   			con s6: sum{i in 1..5}weight[i] = 1;
   			solve noobjective;

			create data omega_RP(drop=i) from [i] s6 = weight ;
		quit;
		/*******************************************************************************************************************/

		proc iml;
			use varcov;
				read all  into varcov[colname=varNames];
			close varcov; 

			use estim_twenty_days;
				read all var{rendement_ABCA rendement_Airbus rendement_BNP rendement_OR rendement_SAN}  into rend[colname=varNames];
			close estim_twenty_days;

			use min_var_weights;
				read all into mvw[colname=varNames];
			close min_var_weights;

			mvw_t = t(mvw);


			return_mv_with_constraints = rend * mvw_t;

			create return_mv_with_constraints from return_mv_with_constraints;
				append from return_mv_with_constraints;
			close return_mv_with_constraints;

			omega_mv_cont = t(mvw);

			create omega_mv_cont from omega_mv_cont;
				append from omega_mv_cont;
			close omega_mv_count;


			use omega_rp;
				read all into rp_weights[colname=varNames];
			close omega_rp;


			return_risk_parity = rend * rp_weights;

			beta = varcov*rp_weights;
			h2 = t(rp_weights)*varcov*rp_weights;

			S1 = rp_weights[1]*beta[1]/h2;
			S2 = rp_weights[2]*beta[2]/h2;
			S3 = rp_weights[3]*beta[3]/h2;
			S4 = rp_weights[4]*beta[4]/h2;
			S5 = rp_weights[5]*beta[5]/h2;

			S_n = S1//S2//S3//S4//S5;

			create return_risk_parity from return_risk_parity;
				append from return_risk_parity;
			close return_risk_parity;

			create S_n from S_n;
				append from S_n;
			close S_n;

		quit;


		data portfolio_naif;
			retain r_1000_naif 1000;
			merge estim_twenty_days return_naif;
			r_1000_naif = r_1000_naif * (1+COL1);
		run;

		data portfolio_mv;
			retain r_1000_mv 1000;
			merge estim_twenty_days return_mv;
			r_1000_mv = r_1000_mv * (1+COL1);
		run;

		data portfolio_mv_with_constraints;
			retain r_1000_mv_wo_c 1000;
			merge estim_twenty_days return_mv_with_constraints;
			r_1000_mv_wo_c = r_1000_mv_wo_c * (1+COL1);
		run;

		data portfolio_RP;
			retain r_1000_rp 1000;
			merge estim_twenty_days return_risk_parity;
			r_1000_rp = r_1000_rp * (1+COL1);
		run;


		proc append base = portfolio_naive_strategy data = portfolio_naif;run;
		proc append base = portfolio_mv_strategy data = portfolio_mv;run;
		proc append base = portfolio_mv_strategy_wcons data = portfolio_mv_with_constraints;run;
		proc append base = portfolio_RP_strategy data = portfolio_RP;run;

		%if &i.=121 %then %do;

			data poids_opt_rp;
				set omega_rp (rename=(s6=s121));
			run;

			data poids_opt_mv;
				set omega_mv (rename=(COL1=COL121));
			run;

			data poids_opt_mv_cont;
				set omega_mv_cont (rename=(COL1=COL121));
			run;

			data contrib_rp;
				set S_n (rename=(COL1=COL121));
			run ;


		%end;

	

		%else %do;

			data poids_opt_rp;
				merge poids_opt_rp omega_rp (rename=(s6=s&i.));
			run;

			data poids_opt_mv;
				merge poids_opt_mv omega_mv (rename=(COL1=COL&i.));
			run;
			data poids_opt_mv_cont;
				merge poids_opt_mv_cont omega_mv_cont (rename=(COL1=COL&i.));
			run;

			data contrib_rp;
				merge contrib_rp S_n (rename=(COL1=COL&i.));
			run;

		%end;

	%end;

%mend;

%automatisation();


data var_cond ; 
	set ohdcc (keep=h1_1 h2_2 h3_3 h4_4 h5_5);
run;
data var_cond;
	merge portfolio (KEEP=date) var_cond;
run;
proc sgplot data=var_cond;
	title "Conditional variances of returns";
	label h1_1="ABC Arbitrage" h2_2="Airbus" h3_3="BNP" h4_4="L'Oréal" h5_5="Sanofi";
	series x=date y=h1_1;
	series x=date y=h2_2;
	series x=date y=h3_3;
	series x=date y=h4_4;
	series x=date y=h5_5;
	yaxis label="Conditional variance";
run;




data poids_opt_mv;
	set poids_opt_mv;
	if _n_=1 then Share="ABC Arbitrage" ;
	if _n_=2 then Share="Airbus" ;
	if _n_=3 then Share="BNP" ;
	if _n_=4 then Share="L'Oréal" ;
	if _n_=5 then Share="Sanofi" ;
run;
proc transpose data=poids_opt_mv out=tr_pd_opt_mv;
	by Share;
run;
proc sgplot data=tr_pd_opt_mv;
	title "Weights of shares in Minimum-Variance Portfolio with short-selling";
	vbar _name_/response=col1 group=Share;
	xaxis label="Date" display=(novalues);
	yaxis display=(nolabel);
run;

data poids_opt_mv_cont;
	set poids_opt_mv_cont;
	if _n_=1 then Share="ABC Arbitrage" ;
	if _n_=2 then Share="Airbus" ;
	if _n_=3 then Share="BNP" ;
	if _n_=4 then Share="L'Oréal" ;
	if _n_=5 then Share="Sanofi" ;
run;
proc transpose data=poids_opt_mv_cont out=tr_pd_opt_mv_cont;
	by Share;
run;
proc sgplot data=tr_pd_opt_mv_cont;
	title "Weights of shares in Minimum-Variance Portfolio without short-selling";
	vbar _name_/response=col1 group=Share;
	xaxis label="Date" display=(novalues);
	yaxis display=(nolabel);
run;

data poids_opt_rp;
	set poids_opt_rp;
	if _n_=1 then Share="ABC Arbitrage" ;
	if _n_=2 then Share="Airbus" ;
	if _n_=3 then Share="BNP" ;
	if _n_=4 then Share="L'Oréal" ;
	if _n_=5 then Share="Sanofi" ;
run;
proc transpose data=poids_opt_rp out=tr_pd_opt_rp;
	by Share;
run;
proc sgplot data=tr_pd_opt_rp;
	title "Weights of shares in Risk Parity Portfolio";
	vbar _name_/response=col1 group=Share seglabel;
	xaxis label="Date" display=(novalues);
	yaxis display=(nolabel);
run;








/*3. Graphiques des contributions des actifs à la volatilité du portefeuille*/
data contrib_rp;
	set contrib_rp;
	if _n_=1 then Share="ABC Arbitrage" ;
	if _n_=2 then Share="Airbus" ;
	if _n_=3 then Share="BNP" ;
	if _n_=4 then Share="L'Oréal" ;
	if _n_=5 then Share="Sanofi" ;
run;
proc transpose data=contrib_rp out=tr_contrib_rp;
	by Share;
run;
proc sgplot data=tr_contrib_rp;
	title "Contributions of shares to portfolio volatility";
	vbar _name_/response=col1 group=Share;
	xaxis label="Date" display=(novalues);
	yaxis display=(nolabel);
run;







/*4. Graphique de rentabilité*/
data rentabilite;
	merge portfolio_naive_strategy (keep= date r_1000_naif) portfolio_mv_strategy (keep=date r_1000_mv) 
			portfolio_mv_strategy_wcons (keep=date r_1000_mv_wo_c) portfolio_rp_strategy (keep=date r_1000_rp) ;
	by date; 
run;
proc sgplot data=rentabilite;
	title "Evolution of our investment";
	label r_1000_naif="Naive Portfolio" r_1000_mv="Minimum Variance Portfolio with short-selling" 
			r_1000_mv_wo_c="Minimum Variance Portfolio without short-selling" r_1000_rp="Risk Parity Portfolio";
	series x=date y=r_1000_naif;
	series x=date y=r_1000_mv;
	series x=date y=r_1000_mv_wo_c;
	series x=date y=r_1000_rp;
	refline 1000 / dataskin = CRISP lineattrs=( color=red);
	yaxis label="Value of our portfolio";
run;

proc sgplot data=portfolio ; 
	title "Returns";
	series x=date y=rendement_ABCA;
	series x=date y=rendement_Airbus;
	series x=date y=rendement_BNP;
	series x=date y=rendement_OR;
	series x=date y=rendement_SAN;
	label rendement_ABCA = "ABC Arbitrage"
		  rendement_Airbus = "Airbus"
		  rendement_BNP = "BNP Paribas"
		  rendement_OR = "L'Oreal"
		  rendement_SAN = "Sanofi";
		  yaxis display=(nolabel);
QUIT;

data ABCAtest;
	set ABCA(rename=(Close=CloseABCA));
run;

data Airbustest;
	set Airbus(rename=(Close=CloseAirbus));
run;

data BNPtest;
	set BNP(rename=(Close=CloseBNP));
run;

data ORtest;
	set OR(rename=(Close=CloseOR));
run;

data SANtest;
	set SAN(rename=(Close=CloseSAN));
run;

data test;
	merge ABCAtest(keep=Date CloseABCA) Airbustest(keep=Date CloseAirbus) BNPtest(keep=Date CloseBNP) ORtest(keep=Date CloseOR) SANtest(keep=Date CloseSAN);
	by Date;
run;
proc sgplot data=test ; 
	title "Evolution in share prices";
	series x=date y=CloseABCA;
	series x=date y=CloseAirbus;
	series x=date y=CloseBNP;
	series x=date y=CloseOR;
	series x=date y=CloseSAN;
	yaxis display=(nolabel);
	label CloseABCA = "ABC Arbitrage"
		  CloseAirbus = "Airbus"
		  CloseBNP = "BNP Paribas"
		  CloseOR = "L'Oreal"
		  CloseSAN = "Sanofi";
QUIT;


/* Finally, we calculate the annual average, volatility and Sharpe ratio for each of our 3 portfolios */

proc means data=portfolio_rp_strategy mean std noprint maxdec=4;
	var col1;
	output out=vol_rp mean=mean_rp std=vol_rp;
run;

proc means data=portfolio_mv_strategy mean std noprint maxdec=4;
	var col1;
	output out=vol_mv mean=mean_mv std=vol_mv;
run;

proc means data=portfolio_mv_strategy_wcons mean std noprint maxdec=4;
	var col1;
	output out=vol_mv_wcons mean=mean_mv_wcons std=vol_mv_wcons;
run;

proc means data=portfolio_naive_strategy mean std noprint maxdec=4 ;
	var col1;
	output out=vol_naif mean=mean_naif std=vol_naif;
run;

data sharpe_rp;
	set vol_rp (keep=mean_rp vol_rp);
	mu_hat_rp=((1+mean_rp)**250-1);
	volat_hat_rp = sqrt(250)*vol_rp;
	sharpe_rp=mu_hat_rp/volat_hat_rp;
	var_hat_rp=volat_hat_rp**2;
	drop mean_rp vol_rp;
run;

Title "Average, variance and volatility of returns and Sharpe ratio for the RP portfolio";
proc print ;
	format mu_hat_rp var_hat_rp sharpe_rp 4.2;
	format volat_hat_rp percent8.2; 
run;

data sharpe_mv;
	set vol_mv (keep=mean_mv vol_mv);
	mu_hat_mv=((1+mean_mv)**250-1);
	volat_hat_mv = sqrt(250)*vol_mv;
	sharpe_mv=mu_hat_mv/volat_hat_mv;
	var_hat_mv=volat_hat_mv**2;
	drop mean_mv vol_mv;
run;

Title "Average, variance and volatility of returns and Sharpe ratio for the MV portfolio without short-selling";
proc print ;
	format mu_hat_mv var_hat_mv sharpe_mv 4.2;
	format volat_hat_mv percent8.2; 
run;

data sharpe_mv_wcons;
	set vol_mv_wcons (keep=mean_mv_wcons vol_mv_wcons);
	mu_hat_mv_wcons=((1+mean_mv_wcons)**250-1);
	volat_hat_mv_wcons = sqrt(250)*vol_mv_wcons;
	sharpe_mv_wcons=mu_hat_mv_wcons/volat_hat_mv_wcons;
	var_hat_mv_wcons=volat_hat_mv_wcons**2;
	drop mean_mv_wcons vol_mv_wcons;
run;

Title "Average, variance and volatility of returns and Sharpe ratio for the MV portfolio no short-selling";
proc print ;
	format mu_hat_mv_wcons var_hat_mv_wcons sharpe_mv_wcons 4.2;
	format volat_hat_mv_wcons percent8.2; 
run;

data sharpe_naif;
	set vol_naif (keep=mean_naif vol_naif);
	mu_hat_naif=((1+mean_naif)**250-1);
	volat_hat_naif = sqrt(250)*vol_naif;
	sharpe_naif=mu_hat_naif/volat_hat_naif;
	var_hat_naif=volat_hat_naif**2;
	drop mean_naif vol_naif;
run;

Title "Average, variance and volatility of returns and Sharpe ratio for the naive portfolio";
proc print ;
	format mu_hat_naif var_hat_naif sharpe_naif 4.2;
	format volat_hat_naif percent8.2; 
run;


