# Poisson averaging limit for low-copy species in multiscale reaction networks

**Setting.** Let $X^N(t)$ be continuous-time Markov chain models of a reaction network with species set $\mathcal{S}$, reactions $y_r\to y_r'$ and intensities $\lambda^N_r$. Assume $N^{-\alpha}X^N(0)\to X_0>0$ for some $\alpha\in\{0,1\}^{|\mathcal{S}|}$, which splits species into **discrete** ones ($\alpha_i=0$, counts $O(1)$) and **continuous** ones ($\alpha_i=1$, counts $O(N)$); write $X^N=(X^N_d,X^N_c)$. With $\beta_r=\max_{S_i\in y_r}\alpha_i$, assume $N^{-\beta_r}\lambda^N_r(v,\lfloor Nw\rfloor)\to\lambda_r(v,w)$ uniformly on compacts, with $\lambda_r$ positive and locally Lipschitz. Let $\mathcal{R}^*=\{y\to y':\pi_c(y)\ne 0\}$ be the fast reactions (sources containing a continuous species). For fixed continuous concentrations $w>0$, the projection of $\mathcal{R}^*$ onto the discrete species defines a stochastic network $\mathcal{S}^w_d$ on the discrete species.

**Assumptions.** (A1) every discrete species is produced or consumed by at least one fast reaction ($\beta_r=1$); (A2) for $y_r\to y_r'\in\mathcal{R}^*$, $\lambda_r(v,w)=\kappa_r(w)\,\frac{v!}{(v-\pi_d(y_r))!}$ with $\kappa_r(w)>0$ for $w>0$, the mass-action system $\mathcal{S}^w_d$ is complex balanced for every $w>0$ with complex-balanced equilibrium $q^w_d$, and its network is irreducible; (A3) the deterministic solution $z(t)$ of the reduced continuous system, whose rates are $\lambda_{c}(w)=\sum\kappa_r(w)(q^w_d)^{\pi_d(y_r)}$ over the fast reactions projected onto the continuous species, exists and stays positive on $[0,T]$ from $\pi_c(X_0)$; (A4) a moment bound $\sup_N\sup_{t\le T}\mathbb{E}[\psi(X^N_d(t))]<\infty$ for some locally bounded $\psi\ge 1$ with $\psi(v)\to\infty$ dominating all $\lambda_r(\cdot,w)$ for $w$ in compacts.

**Theorem (Anderson–Cappelletti–Kurtz, Theorem 3.1).** Under (A1)–(A4),

$$
\sup_{t\in[0,T]}\big|N^{-1}X^N_c(t)-z(t)\big|\xrightarrow[N\to\infty]{}0\quad\text{in probability},
$$

and, with $J^{w}$ a product-form Poisson random vector with mean $q^{w}_d$, for every continuous $g$ with $|g(v)|/\psi(v)\to0$,

$$
\sup_{t\in[0,T]}\Big|\int_0^t\big(g(X^N_d(s))-\mathbb{E}[g(J^{z(s)})]\big)ds\Big|\to 0\ \text{ in probability},\qquad
\sup_{t\in[\delta,T]}\big|\mathbb{E}[g(X^N_d(t))]-\mathbb{E}[g(J^{z(t)})]\big|\to0
$$

for each $\delta\in(0,T)$. So the low-copy species equilibrate instantaneously to the Poisson stationary law of the complex-balanced fast subsystem, slaved to the current continuous concentrations.

**Corollary 3.2.** If the scaled intensities admit two-sided bounds of the form $h_r(w)w^{\pi_c(y_r)}v^{\pi_d(y_r)}\le N^{-\beta_r}\lambda^N_r(v,\lfloor Nw\rfloor)\le\hat h_r(w)v^{\pi_d(y_r)}$ (automatic for suitably rescaled mass-action kinetics) and every complex contains at most one discrete species with coefficient $1$, the same conclusions hold without (A4) for all continuous $g$ of polynomial growth (time-averaged) and all bounded continuous $g$ (fixed times).

## Depends on

- [Complex-balanced concentrations](../complex-balancing-and-the-deficiency-zero-theore/is-complex-balanced.md)

## Proof sketch

This is a stochastic averaging principle in the style of Kurtz: the discrete species form a fast Markov chain whose generator, for frozen $w$, is that of $\mathcal{S}^w_d$. Complex balance makes its stationary law the product-form Poisson distribution with mean $q^w_d$ (Anderson–Craciun–Kurtz). The occupation measure of $X^N_d$ converges to $\int\delta_{s}\otimes\mathrm{Pois}(q^{z(s)}_d)\,ds$, and the continuous species follow the ODE obtained by averaging their rates against this law. Fixed-time convergence for $t\ge\delta$ uses the fast mixing of the discrete chain.

## Sources

- David F. Anderson, Daniele Cappelletti and Thomas G. Kurtz, "Finite Time Distributions of Stochastically Modeled Chemical Systems with Absolute Concentration Robustness", *SIAM Journal on Applied Dynamical Systems* 16 (2017), 1309–1339, <https://doi.org/10.1137/16m1070773>. Preprint version: arXiv:1604.03388 (2016), <https://doi.org/10.48550/arXiv.1604.03388>.
