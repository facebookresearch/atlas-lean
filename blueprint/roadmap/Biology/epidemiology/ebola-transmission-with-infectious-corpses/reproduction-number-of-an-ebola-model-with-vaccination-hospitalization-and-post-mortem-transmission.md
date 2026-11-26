# Reproduction number of an Ebola model with vaccination, hospitalization and post-mortem transmission

**Setting.** Ebola spreads by contact with symptomatic cases, asymptomatic cases and unburied corpses. Consider the compartments susceptible $S$, vaccinated $V$, exposed $E$, symptomatic $I_s$, asymptomatic $I_a$, hospitalized $H$, deceased but not yet safely buried $D$, and recovered $R$, with total living population $N$, recruitment $\Lambda$ and natural death rate $\mu$. With Caputo derivative ${}^CD^\alpha_t$ of order $\alpha\in(0,1]$ ($\alpha=1$ is the ordinary ODE model) and force of infection $\lambda=\beta(I_s+\eta_aI_a+\eta_dD)/N$ (contact rate absorbed into $\beta$),

$$ {}^CD^\alpha_t S=\Lambda-\lambda S+\omega V-(v+\mu)S,\qquad {}^CD^\alpha_t V=vS-(1-\varepsilon)\lambda V-(\mu+\omega)V,$$

$$ {}^CD^\alpha_t E=\lambda[S+(1-\varepsilon)V]-q_2E,\qquad {}^CD^\alpha_t I_s=p\sigma E-q_3I_s,\qquad {}^CD^\alpha_t I_a=(1-p)\sigma E-q_4I_a,$$

$$ {}^CD^\alpha_t H=h_sI_s-q_5H,\qquad {}^CD^\alpha_t D=\delta_sI_s+\delta_hH-q_6D,\qquad {}^CD^\alpha_t R=\gamma_sI_s+\gamma_aI_a+\gamma_hH-\mu R,$$

where $q_2=\mu+\sigma$, $q_3=\gamma_s+\delta_s+h_s+\mu$, $q_4=\gamma_a+\mu$, $q_5=\gamma_h+\delta_h+\mu$ and $q_6=\mu_d$ is the burial rate. Here $v$ is the vaccination rate, $\omega$ waning, $\varepsilon$ vaccine efficacy, $p$ the symptomatic fraction, $h_s$ hospitalization, $\delta_s,\delta_h$ disease deaths, $\eta_a,\eta_d$ relative infectiousness of asymptomatic cases and corpses. The disease-free equilibrium has $S^*=\Lambda q_1/(\mu(q_1+v))$, $V^*=\Lambda v/(\mu(q_1+v))$ with $q_1=\mu+\omega$.

**Theorem.** With $\Psi=\dfrac{S^*+(1-\varepsilon)V^*}{\Lambda/\mu}$, the next generation matrix of the infected subsystem $(E,I_s,I_a,H,D)$ has spectral radius

$$\mathcal{R}_0=\beta\Psi\left[\frac{p\sigma}{q_2q_3}\left(1+\frac{\eta_d(\delta_sq_5+\delta_hh_s)}{q_5q_6}\right)+\frac{\eta_a(1-p)\sigma}{q_2q_4}\right].$$

The disease-free equilibrium is locally asymptotically stable if $\mathcal{R}_0<1$ and unstable if $\mathcal{R}_0>1$; a unique endemic equilibrium with all components positive exists if and only if $\mathcal{R}_0>1$, and the bifurcation at $\mathcal{R}_0=1$ is forward.

The three terms are the contributions of symptomatic infection, of corpses (reached directly from symptomatic cases or via hospital deaths, and infectious for mean time $1/\mu_d$), and of asymptomatic infection. Faster safe burial (larger $\mu_d$) shrinks only the corpse term, which is why safe burial is effective on its own.

## Expansion

Only the force of infection creates new infections, so $F$ has a single non-zero row, $\beta\Psi(0,1,\eta_a,0,\eta_d)$, and $\mathcal{R}_0$ is that row times the first column of $V^{-1}$. The transition matrix $V$ is lower triangular, so its inverse is explicit: an exposed individual becomes symptomatic with probability $p\sigma/q_2$ and spends mean time $1/q_3$ there; a symptomatic case becomes a corpse directly with probability $\delta_s/q_3$ or via hospital with probability $(h_s/q_3)(\delta_h/q_5)$, and the corpse stays infectious for mean time $1/q_6$. Linearization at the disease-free equilibrium and the fractional Routh–Hurwitz (Matignon) criterion, which requires all Jacobian eigenvalues to satisfy $|\arg\lambda|>\alpha\pi/2$, gives the stability threshold.

## Sources

- Noor Muhammad, Md. Nur Alam, Zhang Shiqing, "Mathematical Analysis and Modeling of Ebola Virus Dynamics via Optimal Control and Neural Network Paradigms", arXiv:2511.06303 (2025): Section 2 (Caputo derivative and the fractional Routh–Hurwitz stability lemma), Section 3 (model formulation and parameter groups $q_0,\dots,q_6$), Section 4 (disease-free equilibrium, next-generation matrices $F$, $V$, $V^{-1}$ and the reproduction number, local stability theorem, endemic equilibrium theorem and forward-bifurcation corollary). <https://doi.org/10.48550/arXiv.2511.06303>
