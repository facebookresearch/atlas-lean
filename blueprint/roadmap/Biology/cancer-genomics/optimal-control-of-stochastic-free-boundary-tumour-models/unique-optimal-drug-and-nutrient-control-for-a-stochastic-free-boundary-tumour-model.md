# Unique optimal drug and nutrient control for a stochastic free-boundary tumour model

**Setting.** A radially symmetric tumour occupies $\{|x|<R(t)\}\subset\mathbb{R}^3$ and contains proliferating, quiescent and dead cells with densities $P,Q,D$, $P+Q+D=N$, moving with a radial velocity field $v$; nutrient $C$ and drug $W$ diffuse and are consumed. In the deterministic model, $C_t=D_1\Delta C-(K_1(C)P+K_2(C)Q)$ and $W_t=D_2\Delta W-(K_3(W)P+K_4(W)Q)$ with boundary values $\bar C(t),\bar W(t)$ on $|x|=R(t)$; $P,Q,D$ obey transport equations $\partial_t P+\mathrm{div}(Pv)=[K_B-K_Q-K_A-G_1(W)]P+K_PQ$ and analogous equations for $Q,D$ with rates depending on $C$ (proliferation, quiescence, apoptosis, recruitment, necrosis) and drug kill rates $G_1,G_2$; summing gives $\mathrm{div}\,v=(K_BP-K_RD)/N$ and $R'(t)=v(R(t),t)$. After the change of variables $\rho=|x|/R(t)$, $\eta=R$, the stochastic model adds multiplicative noise to every equation, e.g.

$$dc=\Big[D_1\rho^{-2}\partial_\rho(\rho^2\partial_\rho c)+u(1,\tau)\rho\,\partial_\rho c-\eta^2f(c,p,q)\Big]d\tau+c\sum_{i=0}^m h^1_i(\rho)\,dB_i,$$

with an $m$-dimensional Brownian motion $B$ and similar terms for $w,p,q,a,\eta$. The controls are an interior nutrient source $u_1$ and drug source $u_2$ and the boundary supplies $\bar c,\bar w$, each in a box $[l_i^*,l_i^{**}]$, and the cost is

$$J=\int_0^1\!\!\int_0^T\rho^2\big(\lambda_1p^2+\lambda_2q^2+(u_1-r_1^*)^2+(u_2-r_2^*)^2\big)\,d\tau\,d\rho+\int_0^T\big((\bar c-r_3^*)^2+(\bar w-r_4^*)^2\big)d\tau.$$

**Theorem.** Under the model's regularity assumptions and compatible non-negative initial data:

1. For almost every sample path the stochastic system has a unique solution for every $T>0$, with $\eta\in C[0,T]$, $c,w$ continuous on the unit ball cylinder and $p,q,a$ continuous on $[0,1]\times[0,T]$, all adapted to the Brownian filtration; the solution map is Lipschitz in the controls.
2. The stochastic adjoint system has a unique adapted solution, Lipschitz in the controls.
3. There is $T>0$ such that the stochastic optimal control problem has a unique optimal control, adapted to the filtration, characterized by the projection formulas

$$u_1^*=\mathcal{F}_1(-z_c+r_1^*),\quad u_2^*=\mathcal{F}_2(-z_w+r_2^*),\quad \bar c^*=\mathcal{F}_3\big(D_1\partial_\rho z_c(1,\cdot)+r_3^*\big),\quad \bar w^*=\mathcal{F}_4\big(D_2\partial_\rho z_w(1,\cdot)+r_4^*\big),$$

where $z_c,z_w$ are adjoint states and $\mathcal{F}_i$ clips its argument to $[l_i^*,l_i^{**}]$. The stochastic optimal control also minimizes the expected cost, and the deterministic expected-cost problem has a unique optimal control; analogous results hold with correlated Brownian motions.

## Expansion

The key device is a pathwise change of variables: multiplying each unknown by an exponential of the noise, $c=e^{\sum_i h^1_iB_i-\frac12(\cdot)\tau}\tilde c$ and similarly for the others, turns the multiplicative-noise system into a random but deterministic-in-form PDE system for almost every $\omega$. Deterministic parabolic estimates (Hölder and $W^{2,1}_p$ theory for the nutrient and drug equations, characteristics for the transport equations) and a contraction argument then give pathwise well-posedness. For the control problem, Lipschitz dependence of states and adjoints on the controls with constants of order $T$ makes the optimality map a contraction for small $T$, giving existence and uniqueness, while Ekeland's variational principle yields the necessary conditions for an approximate minimizer that pass to the limit.

## Sources

- Sakine Esmaili, M. R. Eslahchi, Delfim F. M. Torres, "Optimal control for a nonlinear stochastic PDE model of cancer growth", arXiv:2307.09574 (2023): Section 2 (Ekeland's variational principle, function spaces, auxiliary existence lemmas), Section 3 (deterministic free-boundary tumour model, stochastic model, existence and uniqueness theorem), Section 4 (cost functional, Lipschitz estimates for states and adjoints, adjoint existence theorem, necessary conditions, existence and uniqueness of the stochastic optimal control, correlated-noise extension). <https://doi.org/10.48550/arXiv.2307.09574> Published version: Optimization 73 (2024), no. 9, 2745--2789, <https://doi.org/10.1080/02331934.2023.2232141>.
