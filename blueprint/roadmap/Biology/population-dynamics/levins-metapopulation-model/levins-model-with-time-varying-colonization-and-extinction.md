# Levins model with time-varying colonization and extinction

**Setting.** The fraction $p(t)$ of occupied habitat patches satisfies the nonautonomous Levins equation

$$p' = c(t)\,p(1-p) - e(t)\,p,$$

where the colonization rate $c$ and extinction rate $e$ are bounded, continuous and positive, with $c(t)\ge c_*>0$. Let $\mathcal{D}(t) = e(t)-c(t)$, $\Phi(t,s) = \exp\!\big(\int_s^t\mathcal{D}(r)\,dr\big)$, and let $\Sigma(\mathcal{D}) = [\beta^-(\mathcal{D}),\beta^+(\mathcal{D})]$ be the exponential dichotomy spectrum of the scalar linear equation $x' = \mathcal{D}(t)x$ on $[0,\infty)$ (for constant rates it is the single point $e-c$).

**Theorem.** For $p(0)>0$,

$$p(t) = \frac{1}{\Phi(t,0)\,p(0)^{-1} + \int_0^t\Phi(t,s)\,c(s)\,ds},$$

and:

1. If $\beta^+(\mathcal{D})<0$ (colonization uniformly dominates extinction), then $p(t) = \big(\int_0^t\Phi(t,s)c(s)\,ds + o(1)\big)^{-1}$ with an exponentially decaying error, so every solution with $p(0)>0$ is asymptotically equal to $\big(\int_0^t\Phi(t,s)c(s)\,ds\big)^{-1}$, which does not depend on the initial condition.
2. If $\beta^-(\mathcal{D})>0$ (extinction uniformly dominates), then $p(t)\le Le^{-\eta t}$ for some $L\ge1$, $\eta>0$: the metapopulation goes extinct exponentially fast.
3. If $0\in[\beta^-(\mathcal{D}),\beta^+(\mathcal{D})]$, then $\liminf_{t\to\infty}p(t) = 0$.

## Expansion

The substitution $u=1/p$ linearises the Bernoulli equation to $u' = \mathcal{D}(t)u + c(t)$, whose variation-of-constants solution gives the formula. When the linear part has an exponential dichotomy with negative spectrum, $\Phi(t,0)\to0$ exponentially and the integral term is a bounded, positive attracting solution of the $u$-equation; when the spectrum is positive, $u$ grows exponentially and $p=1/u$ decays. Constant rates recover the classical threshold $p^* = 1-e/c$ for $c>e$.

## Sources

- G. Robledo, R. Bustamante, "Generalizing the Levins metapopulation model to time varying colonization and extinction rates", *Journal of Mathematical Biology* 93(6) (2026), 67, Propositions 1–2 and Theorems 1–2, <https://doi.org/10.1007/s00285-026-02485-0> (preprint arXiv:2504.20396).
