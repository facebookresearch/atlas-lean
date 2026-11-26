# Stability of the composite rarefaction–viscous shock wave in the hyperbolic Keller–Segel model

The Levine–Sleeman–Nilsen-Hamilton angiogenesis model with logarithmic sensitivity, $n_t=Dn_{xx}-\chi(n(\ln c)_x)_x$, $c_t=-nc+\beta c$, describes endothelial cell density $n>0$ and VEGF concentration $c>0$. The Hopf–Cole-type substitution $q=-(\ln c)_x$ followed by rescaling turns it into the parabolic–hyperbolic system

$$n_t-(nq)_x=n_{xx},\qquad q_t-n_x=0,\qquad x\in\mathbb R,\ t>0,$$

with $(n,q)(x,0)\to(n_\pm,q_\pm)$ as $x\to\pm\infty$, $n_\pm>0$. The inviscid part $n_t-(nq)_x=0$, $q_t-n_x=0$ is strictly hyperbolic on $\{n>0\}$, with eigenvalues $\lambda_{1,2}(n,q)=\tfrac12\big(-q\mp\sqrt{q^2+4n}\big)$, right eigenvectors $r_k=(-\lambda_k,1)^{\mathsf T}$, and genuinely nonlinear characteristic fields.

Let $(n_m,q_m)$ be an intermediate state with $(n_m,q_m)\in R_1(n_-,q_-)$ (reachable from $(n_-,q_-)$ by a 1-rarefaction) and $(n_m,q_m)\in S_2(n_+,q_+)$ (connected to $(n_+,q_+)$ by an admissible 2-shock). Let $(n^r,q^r)(x/t)$ be the 1-rarefaction from $(n_-,q_-)$ to $(n_m,q_m)$, and let $(\tilde n^S,\tilde q^S)(x-\sigma t)$ be the 2-viscous shock profile of the parabolic–hyperbolic system from $(n_m,q_m)$ to $(n_+,q_+)$.

**Theorem.** For each $(n_+,q_+)$ with $n_+>0$ there are $\delta_0,\delta_1>0$ such that, if $|n_+-n_m|+|n_m-n_-|\le\delta_0$ and

$$\sum_\pm\|(n_0-n_\pm,q_0-q_\pm)\|_{L^2(\mathbb R_\pm)}+\|(n_{0x},q_{0x})\|_{L^2(\mathbb R)}\le\delta_1,$$

then there is a unique global solution and an absolutely continuous shift $\mathbf X(t)$ with

$$\sup_{x\in\mathbb R}\Big|(n,q)(t,x)-\big(n^r(\tfrac xt)+\tilde n^S(x-\sigma t-\mathbf X(t))-n_m,\ q^r(\tfrac xt)+\tilde q^S(x-\sigma t-\mathbf X(t))-q_m\big)\Big|\xrightarrow[t\to\infty]{}0,$$

and $\mathbf X(t)/t\to0$. The difference from the composite wave lies in $C((0,\infty);H^1)$, and $n_{xx}-\tilde n^S_{xx}(\cdot-\sigma t-\mathbf X)\in L^2(0,\infty;L^2)$.

## Expansion

Viscous shocks of systems are usually stable only with a shift that is fixed in advance by conservation of mass. That rule is unavailable when a rarefaction is present, because the rarefaction carries mass away. The method of $a$-contraction with shifts (Kang–Vasseur) instead lets $\mathbf X(t)$ evolve by an ODE chosen to cancel the bad terms in a weighted relative-entropy estimate around the shock. The weight is tied to the shock profile, and the rarefaction contributes good expansive terms through $\partial_x\lambda_1(n^r)>0$. Higher-order estimates use the parabolic dissipation $n_{xx}$, since $q$ has no diffusion. The sublinear growth $\mathbf X(t)/t\to0$ shows that the shock keeps its Rankine–Hugoniot speed $\sigma$ asymptotically. This links the angiogenesis model to the theory of Riemann-problem wave patterns: the time-asymptotic profile of the chemotactic invasion is the generic Riemann pattern of its inviscid limit.

## Sources

- Sitong Liu, Jingyu Li, "Nonlinear stability of composite waves of traveling wave and rarefaction wave for a parabolic-hyperbolic system arising from chemotaxis", arXiv:2609.23448 (2026), Section 1 (system and Riemann problem), Theorem 1.1, Propositions 3.1–3.2, <https://doi.org/10.48550/arXiv.2609.23448>.
