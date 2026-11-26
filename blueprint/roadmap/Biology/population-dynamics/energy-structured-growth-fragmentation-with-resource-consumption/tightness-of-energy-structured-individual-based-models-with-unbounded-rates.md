# Tightness of energy-structured individual-based models with unbounded rates

**Model.** The population is a finite point measure $\mu_t=\sum_i\delta_{x_i(t)}$ on energies $x>0$, and $R_t\in[0,R_{\max}]$ is the resource. Between jumps each energy follows $\dot x=g(x,R_t)$ (growth if positive, degrowth if negative) and the resource follows $\dot R=\rho(R,\mu)$. An individual of energy $x$ dies at rate $d(x)$ and reproduces at rate $b(x)$ by fragmentation: it is replaced by an offspring of fixed energy $x_0>0$ and a parent of energy $x-x_0$. The renormalized processes $(\mu^K_t,R^K_t)$ give each individual mass $1/K$ with resource consumption scaled accordingly.

**Assumptions.**

- (H0) $g(x,0)<0<g(x,R_{\max})$ for all $x>0$;
- (H1) $\int_0^x d(t)/g(t,0)\,dt=-\infty$ for all $x>0$ (starving individuals die before reaching zero energy);
- (H2) a positive non-decreasing weight $\omega\in C^1$, Lipschitz on $(1,\infty)$, with $\sup_R|g(x,R)|\le c_g\omega(x)$, $b(x)\le c_b\omega(x)$ for $x>1$, and $d(x)\omega(x)\le c_d$;
- (H3) $\mu^K_0\to\mu^*_0$ in law in the space $\mathcal M_\omega$ of measures integrating $\omega$, with the weak topology;
- (H4) $\sup_K\mathbb E\,\langle\mu^K_0,1+\mathrm{Id}+\omega\rangle^p<\infty$ for some $p>1$.

**Theorem.** Under (H0)–(H4), for every $T\ge0$ the sequence $(\mu^K_t,R^K_t)_{t\le T}$ is tight in $\mathbb D([0,T],\mathcal M_\omega\times[0,R_{\max}])$. Every accumulation point is continuous and satisfies $R^*_t=R^*_0+\int_0^t\rho(R^*_s,\mu^*_s)\,ds$ and, for test functions $\varphi_t(x)$ dominated by $\omega$,
$$\langle\mu^*_t,\varphi_t\rangle=\langle\mu^*_0,\varphi_0\rangle+\int_0^t\!\!\int\Big(\partial_s\varphi_s+g(x,R^*_s)\partial_x\varphi_s+b(x)\big(\varphi_s(x_0)+\varphi_s(x-x_0)-\varphi_s(x)\big)-d(x)\varphi_s(x)\Big)\mu^*_s(dx)\,ds,$$
the weak form of a growth–fragmentation PDE coupled to the resource.

**Well-posedness.** Under the same structural assumptions the stochastic process itself is almost surely defined for all times: there is no explosion of the number of jumps, and $\mathbb E\sup_{t\le T}(E_t+N_t+\Omega_t)<\infty$ for total energy $E_t$, population size $N_t$ and total weight $\Omega_t=\langle\mu_t,\omega\rangle$.

## Expansion

The danger with unbounded rates is explosion: large individuals reproduce and grow arbitrarily fast. Total energy is controlled because fragmentation conserves it and growth is fueled by a bounded resource, so $R_t+E_t\le R_0+E_0+Ct$. The weight $\omega$ dominates the growth speed and birth rate while $d\,\omega$ is bounded, which makes $\langle\mu_t,\omega\rangle$ a semimartingale with controlled drift; Aldous–Rebolledo criteria then give tightness in the $\omega$-weighted weak topology, and the martingale parts vanish as $K\to\infty$. (H1) prevents individuals from piling up at zero energy.

## Sources

- V. Brodu, "Individual-based stochastic model with unbounded growth, birth and death rates: a tightness result", arXiv:2603.21634 (2026), Theorem 1.1, Section 2 (Propositions 2.5 and 2.12, Corollaries 2.8 and 2.13, Corollary 2.15), Section 3, <https://doi.org/10.48550/arXiv.2603.21634>.
