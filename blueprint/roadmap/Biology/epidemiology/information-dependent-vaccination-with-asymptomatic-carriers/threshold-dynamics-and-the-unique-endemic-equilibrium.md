# Threshold dynamics and the unique endemic equilibrium

**Model (Eqs. 3a–3f).** Susceptible $S$, exposed $E$, asymptomatic infectious $I_a$, symptomatic infectious $I_s$, vaccinated $V$ and an information index $M$ evolve as

$$\begin{aligned}\dot S&=\Lambda-(\varphi_0+\varphi_1(M))S-\beta S(\varepsilon_aI_a+\varepsilon_sI_s)-\mu S,\\ \dot E&=\beta(S+\sigma V)(\varepsilon_aI_a+\varepsilon_sI_s)-(\rho+\mu)E,\\ \dot I_a&=\rho E-(\eta+\nu_a+\mu)I_a,\\ \dot I_s&=\eta I_a-(\nu_s+\delta+\mu)I_s,\\ \dot V&=(\varphi_0+\varphi_1(M))S-\sigma\beta V(\varepsilon_aI_a+\varepsilon_sI_s)-\mu V,\\ \dot M&=a(kI_s-M),\end{aligned}$$

with positive parameters, vaccine failure factor $\sigma\in[0,1)$, constant vaccination rate $\varphi_0>0$, and a continuous increasing information-driven rate $\varphi_1$ with $\varphi_1(0)=0$ and $\sup\varphi_1<1-\varphi_0$. The disease-free equilibrium is $\bigl(\bar S,0,0,0,\bar V,0\bigr)$ with $\bar S=\Lambda/(\mu+\varphi_0)$, $\bar V=\Lambda\varphi_0/(\mu(\mu+\varphi_0))$.

**Propositions 1, 3, 4 and 6.**
- The region $\mathcal{D}=\{0<S+E+I_a+I_s+V\le\Lambda/\mu,\ 0<S\le\Lambda/(\mu+\varphi_0),\ 0<S+\sigma V\le\Lambda(\mu+\sigma\varphi_0)/(\mu(\mu+\varphi_0)),\ M\le k\Lambda/\mu\}$ is positively invariant.
- With $R_V$ the control reproduction number, the disease-free equilibrium is locally asymptotically stable if $R_V<1$ and unstable if $R_V>1$; it is globally asymptotically stable in $\mathcal{D}$ if $R_V<1$.
- If $R_V\le1$ there is no endemic equilibrium; if $R_V>1$ there is exactly one.

At $R_V=1$ the system undergoes a transcritical bifurcation in the transmission rate $\beta$ at $\beta_c$ solving $R_V(\beta_c)=1$; its direction is read from the signs of the center-manifold coefficients $A$ and $B$ (Eqs. 12–13), backward when $A>0$ and $B>0$.

## Depends on

- [Control reproduction number and critical vaccination rate](control-reproduction-number-and-critical-vaccination-rate.md)

## Expansion

Local stability follows from the next-generation threshold theorem once $R_V$ is computed at the disease-free equilibrium, where $M=0$ and $\varphi_1(0)=0$. For the invariant region, the living non-recovered population $N=S+E+I_a+I_s+V$ satisfies $\dot N\le\Lambda-\mu N$, and then $\dot M\le a(k\Lambda/\mu-M)$. The source proves global stability of the disease-free equilibrium (two alternative proofs) and existence and uniqueness of the endemic equilibrium in its supplementary material; information-driven vaccination shifts the endemic level but not the threshold.

## Sources

- B. Buonomo, R. Della Marca, A. d'Onofrio, M. Groppi, "A behavioural modelling approach to assess the impact of COVID-19 vaccine hesitancy", Journal of Theoretical Biology (2022) 110973. <https://doi.org/10.1016/j.jtbi.2021.110973>, PMCID PMC8651553. Section 3, Propositions 1, 3, 4 and 6, Eqs. (6) and (12)–(13).
