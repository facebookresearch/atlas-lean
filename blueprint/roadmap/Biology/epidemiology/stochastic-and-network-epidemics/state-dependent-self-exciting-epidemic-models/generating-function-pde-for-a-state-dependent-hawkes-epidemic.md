# Generating-function PDE for a state-dependent Hawkes epidemic

In the early phase of an epidemic, when the susceptible pool is effectively infinite, let $C_t$ be the cumulative number of infections, $I_t$ the current infecteds and $R_t$ the recovereds. $C_t$ is a self-exciting counting process with stochastic intensity

$$
\Lambda_t=\lambda^\infty(I_t,R_t)+\int_0^tQ_se^{-r(t-s)}\,dC_s,\qquad \lambda^\infty(i,\rho)=\lambda_0+i\log\alpha+\rho\log\beta,
$$

with $\alpha>1$ and $\beta,\lambda_0,r>0$. The $Q_n$ are i.i.d. nonnegative marks (quarantine levels of successive infecteds), independent of everything else. Each infected recovers after an independent $\mathrm{Exp}(\mu)$ time. Then $(I_t,R_t,\Lambda_t)$ is Markov, and the joint transform

$$
\varphi(t,z,w,s)=\mathbb E\big[z^{I_t}w^{R_t}e^{-s\Lambda_t}\big],\qquad |z|,|w|\le1,\ s\ge0,
$$

solves the first-order linear PDE

$$
\partial_t\varphi+\Big[rs-1+\alpha^{-s}M_Q(s)\,z\Big]\partial_s\varphi+\Big[(\mu+rs\log\alpha)z-\mu\Big(\frac\alpha\beta\Big)^sw\Big]\partial_z\varphi+\big[rs\log\beta\big]w\,\partial_w\varphi=-\lambda_0rs\,\varphi,
$$

with $\varphi(0,z,w,s)=z^{i_0}e^{-s(\lambda_0+i_0\log\alpha)}$ and $M_Q(s)=\mathbb E[e^{-sQ}]$. Along its characteristics, the PDE reduces to a system of ordinary differential equations, from which exact moments of $I_t$ and $R_t$ follow. These moments capture the overdispersion that independent-infection SIR chains cannot produce.

## Proof sketch

Between events, $\Lambda$ decays toward the current baseline at rate $r$, which gives the $rs$ drift terms. An infection, at rate $\Lambda$, adds one to $I$ and raises $\Lambda$ by $Q+\log\alpha$; this produces the factor $z\alpha^{-s}M_Q(s)$. A recovery, at rate $\mu I$, moves one individual from $I$ to $R$ and shifts the baseline by $\log\beta-\log\alpha$, giving $\mu(\alpha/\beta)^sw$. Collecting the generator terms against $z^iw^\rho e^{-s\lambda}$ gives the PDE. The density of $(I_t,R_t,\Lambda_t)$ obeys the corresponding partial difference–differential equation.

## Sources

- Jonathan A. Chávez Casillas, "A stochastic model for the early stages of highly contagious epidemics by using a state-dependent point process", *Communications in Nonlinear Science and Numerical Simulation* 136 (2024), 108100, <https://doi.org/10.1016/j.cnsns.2024.108100>. Preprint version: arXiv:2209.08612 (2022), Section 2 (intensity (intensityC), baseline and kernel assumptions), Theorems 3–4 and Corollary 5, <https://doi.org/10.48550/arXiv.2209.08612>.
