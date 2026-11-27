# Control reproduction number and critical vaccination rate

**Model (Eqs. 3a–3f).** Susceptible $S$, exposed $E$, asymptomatic infectious $I_a$, symptomatic infectious $I_s$, vaccinated $V$ and an information index $M$ evolve as

$$\begin{aligned}\dot S&=\Lambda-(\varphi_0+\varphi_1(M))S-\beta S(\varepsilon_aI_a+\varepsilon_sI_s)-\mu S,\\ \dot E&=\beta(S+\sigma V)(\varepsilon_aI_a+\varepsilon_sI_s)-(\rho+\mu)E,\\ \dot I_a&=\rho E-(\eta+\nu_a+\mu)I_a,\\ \dot I_s&=\eta I_a-(\nu_s+\delta+\mu)I_s,\\ \dot V&=(\varphi_0+\varphi_1(M))S-\sigma\beta V(\varepsilon_aI_a+\varepsilon_sI_s)-\mu V,\\ \dot M&=a(kI_s-M),\end{aligned}$$

with positive parameters, vaccine failure factor $\sigma\in[0,1)$, constant vaccination rate $\varphi_0>0$, and a continuous increasing information-driven rate $\varphi_1$ with $\varphi_1(0)=0$ and $\sup\varphi_1<1-\varphi_0$. The disease-free equilibrium is $\bigl(\bar S,0,0,0,\bar V,0\bigr)$ with $\bar S=\Lambda/(\mu+\varphi_0)$, $\bar V=\Lambda\varphi_0/(\mu(\mu+\varphi_0))$.

**Proposition 2.** The basic reproduction number (no vaccination) and the control reproduction number are

$$R_0=\frac{\rho\beta\Lambda\bigl(\varepsilon_a(\nu_s+\delta+\mu)+\varepsilon_s\eta\bigr)}{\mu(\rho+\mu)(\eta+\nu_a+\mu)(\nu_s+\delta+\mu)},\qquad R_V=R_0\,\frac{\mu+\sigma\varphi_0}{\mu+\varphi_0}=R_0\bigl(1-(1-\sigma)p\bigr),$$

where $p=\bar V/(\bar S+\bar V)=\varphi_0/(\mu+\varphi_0)$ is the vaccinated fraction at the disease-free equilibrium. Thus $R_V\le R_0$, with equality only if $\varphi_0=0$ or $\sigma=1$.

**Proposition 5 (critical vaccination).** Let $\varphi_0^c=\mu(R_0-1)/(1-\sigma R_0)$.
- If $0\le\sigma<1/R_0$ and $\varphi_0\ge\varphi_0^c$, the disease is eliminated (the disease-free equilibrium is globally asymptotically stable).
- If $\sigma\ge1/R_0$, no constant vaccination rate prevents an outbreak.
- If $0<\varphi_0<\varphi_0^c$, the disease-free equilibrium is unstable.

Equivalently, elimination requires $p>p_c=\dfrac{1}{1-\sigma}\Bigl(1-\dfrac{1}{R_0}\Bigr)$. The information-dependent term $\varphi_1$ does not enter $R_V$ because $M=0$ at the disease-free equilibrium.

## Depends on

- [Basic reproduction number of the next-generation matrix](../../next-generation-matrix-and-the-basic-reproductio/r0.md)

## Expansion

An exposed individual becomes asymptomatic infectious with probability $\rho/(\rho+\mu)$, stays infectious for mean time $1/(\eta+\nu_a+\mu)$ at relative infectiousness $\varepsilon_a$, and progresses to the symptomatic class with probability $\eta/(\eta+\nu_a+\mu)$, where it is infectious for mean time $1/(\nu_s+\delta+\mu)$ at relative infectiousness $\varepsilon_s$. Multiplying by the force of infection on the effective susceptible pool $\bar S+\sigma\bar V=\Lambda(\mu+\sigma\varphi_0)/(\mu(\mu+\varphi_0))$ gives $R_V$, and setting $\varphi_0=0$ (pool $\Lambda/\mu$) gives $R_0$; this is the spectral radius of the next-generation matrix. Solving $R_V<1$ for $\varphi_0$ gives $\varphi_0(1-\sigma R_0)>\mu(R_0-1)$, which is the case split above.

## Sources

- B. Buonomo, R. Della Marca, A. d'Onofrio, M. Groppi, "A behavioural modelling approach to assess the impact of COVID-19 vaccine hesitancy", Journal of Theoretical Biology (2022) 110973. <https://doi.org/10.1016/j.jtbi.2021.110973>, PMCID PMC8651553. Section 3, Propositions 2 and 5, Eqs. (7)–(11).
