# Poisson limit of absolute-concentration-robust species

**Absolute concentration robustness.** A species $S_i$ has ACR in a deterministic reaction system if all positive equilibria share the same value $q_i$ of its concentration; the system is a non-degenerate ACR system if it has at least two positive equilibria. Deterministically, an ACR species returns to $q_i$ whatever the total amounts; stochastic models with conservation laws instead go extinct eventually, so the relevant question is the distribution on finite time intervals when the other species are abundant.

**Setting.** Let $X^N(t)$ be continuous-time Markov chain models of a reaction network with species set $\mathcal{S}$, reactions $y_r\to y_r'$ and intensities $\lambda^N_r$. Assume $N^{-\alpha}X^N(0)\to X_0>0$ for some $\alpha\in\{0,1\}^{|\mathcal{S}|}$, which splits species into **discrete** ones ($\alpha_i=0$, counts $O(1)$) and **continuous** ones ($\alpha_i=1$, counts $O(N)$); write $X^N=(X^N_d,X^N_c)$. With $\beta_r=\max_{S_i\in y_r}\alpha_i$, assume $N^{-\beta_r}\lambda^N_r(v,\lfloor Nw\rfloor)\to\lambda_r(v,w)$ uniformly on compacts, with each $\lambda_r$ not identically zero and locally Lipschitz. Let $\mathcal{R}^*=\{y\to y':\pi_c(y)\ne 0\}$ be the fast reactions (sources containing a continuous species). For fixed continuous concentrations $w>0$, the projection of $\mathcal{R}^*$ onto the discrete species defines a stochastic network $\mathcal{S}^w_d$ on the discrete species.

Let $\widetilde{\mathcal{S}}$ be the system with reactions $\mathcal{R}^*$ and deterministic kinetics $\tilde\lambda_r(v,w)=\kappa_r(w)v^{\pi_d(y_r)}$. Assume, besides (A1)–(A3) of the multiscale Poisson averaging theorem, that $\widetilde{\mathcal{S}}$ is a non-degenerate ACR system in which some ACR species are discrete; let $X^N_{\mathrm{acr}}$ be the counts of the discrete ACR species, $q$ their ACR values, and $J\sim\mathrm{Pois}(q)$ (product form). Assume also the two-sided intensity bounds and that each complex contains at most one discrete species, with coefficient $1$.

**Corollary (Anderson–Cappelletti–Kurtz, Corollary 4.1).** If $\pi_c(X_0)$ is a positive equilibrium of the reduced continuous system, then for every continuous $\hat g$ of polynomial growth and every bounded continuous $\hat\varphi$, $\delta\in(0,T)$,

$$
\sup_{t\le T}\Big|\int_0^t\big(\hat g(X^N_{\mathrm{acr}}(s))-\mathbb{E}[\hat g(J)]\big)ds\Big|\to0\ \text{in probability},\qquad
\sup_{t\in[\delta,T]}\big|\mathbb{E}[\hat\varphi(X^N_{\mathrm{acr}}(t))]-\mathbb{E}[\hat\varphi(J)]\big|\to0 .
$$

In particular $P(X^N_{\mathrm{acr}}(t)\in A)\to P(J\in A)$ uniformly on $[\delta,T]$: the ACR species are asymptotically Poisson with mean equal to the ACR value.

**Corollary 4.2.** If $\pi_c(X_0)$ lies only in the basin of attraction of an equilibrium of the reduced continuous system, the same holds with $J$ replaced by $J^{z(t)}\sim\mathrm{Pois}(q^{z(t)}_d)$, and $q^{z(t)}_d\to q$ as $t\to\infty$.

**Example.** For $A+B\xrightarrow{\kappa_1}2B$, $B\xrightarrow{\kappa_2}A$, species $A$ has ACR value $\kappa_2/\kappa_1$. If $X^N_A(0)$ stays bounded and $X^N_B(0)/N\to b>0$, then on any finite time window $X^N_A(t)$ is asymptotically $\mathrm{Pois}(\kappa_2/\kappa_1)$, both in time average and at fixed times.

## Depends on

- [Poisson averaging limit for low-copy species in multiscale reaction networks](poisson-averaging-limit-for-low-copy-species-in-multiscale-reaction-networks.md)

## Proof sketch

At a positive equilibrium $w^*$ of the reduced continuous system, $(q^{w^*}_d,w^*)$ is a positive equilibrium of $\widetilde{\mathcal{S}}$, so the ACR coordinates of $q^{w^*}_d$ equal $q$ regardless of $w^*$. Applying the averaging theorem with test functions depending only on the ACR coordinates gives the Poisson limit. In the basin case, continuity of the complex-balanced equilibrium $q^w_d$ in $w$ transfers the convergence $z(t)\to w^*$ to the Poisson parameters.

## Sources

- David F. Anderson, Daniele Cappelletti and Thomas G. Kurtz, "Finite Time Distributions of Stochastically Modeled Chemical Systems with Absolute Concentration Robustness", *SIAM Journal on Applied Dynamical Systems* 16 (2017), 1309–1339, <https://doi.org/10.1137/16m1070773>. Preprint version: arXiv:1604.03388 (2016), <https://doi.org/10.48550/arXiv.1604.03388>.
