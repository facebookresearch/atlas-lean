# Exponential survival and strong survival of the SIRS process on sparse random graphs

**Model.** On a graph $G$, the SIRS process with infection rate $\lambda > 0$, recovery rate $1$ and deimmunization rate $\alpha > 0$ is the continuous-time Markov chain in which each infected vertex infects each susceptible neighbour at rate $\lambda$, each infected vertex recovers at rate $1$, and each recovered vertex becomes susceptible again at rate $\alpha$. As $\alpha \to \infty$ it becomes the SIS contact process; unlike SIS it is not attractive. Write $\hat p = p/(p + 1)$. Let $\mathcal G_{\mathrm{conf}}(n, \mu)$ be the configuration model with i.i.d. degrees $D \sim \mu$, and $GW(\mu)$ the Galton–Watson tree with offspring law $\mu$.

**Theorem.**
1. *(Exponential survival.)* If $\mathbb{E}[D(D - 2)] > 0$, there is $c_\mu \ge 0$ such that for $\alpha > c_\mu$ and $\lambda > c_\mu$ the SIRS process on $\mathcal G_{\mathrm{conf}}(n, \mu)$ started from all vertices infected survives for time $\exp(\Theta(n))$ with high probability.
2. *(No subcritical phase for heavy tails.)* If $\mathbb{E}D = d \in (1, \infty)$ and there is $f : \mathbb N \to \mathbb R^+$ with $\limsup_{M \to \infty} M^2 \mu([M, f(M)]) = \infty$ (for example power laws with exponent in $(2, 3)$), then $c_\mu = 0$: for every $\lambda, \alpha > 0$ the survival time is $\exp(\Theta(n))$ w.h.p.
3. *(Strong survival on trees.)* Suppose $\mu$ has unbounded support, $d = \mathbb{E}D > 1$, $\hat\alpha > 1/\sqrt d$, and $\limsup_n \mu([n, \infty))\, e^{n^{\alpha - \delta}} = \infty$ for some $\delta > 0$. If

$$\lambda > \frac{\alpha + 2}{\alpha + 1}\left(\hat\alpha\sqrt d - 1\right)^{-1},$$

then for any tree obtained by attaching $GW(\mu)$ at a vertex $\rho$, and any initial configuration with finitely many infections including $\rho$, the root is re-infected infinitely often with probability at least $p(\mu, \lambda, \alpha) > 0$. This holds for $\mu = \mathrm{Pois}(d)$, $d > 1$, $\alpha > \max(1, 1/(\sqrt d - 1))$.

## Expansion

A vertex of large degree that keeps cycling through $S \to I \to R \to S$ acts as a local reservoir: during each infectious period it reinfects a constant fraction of its susceptible neighbours, which in turn reinfect it after it loses immunity. Exponential survival on finite graphs comes from linking such reservoirs through paths that transmit the infection with probability bounded below, so extinction requires $\Theta(n)$ independent failures. Heavy tails provide enough hubs for every $\lambda, \alpha$. On trees, strong survival (local recurrence at the root) is subtler than for SIS, since raising $\lambda$ alone does not help on a star; the condition balances the reinfection rate $\hat\lambda$ through low-degree bottlenecks against the waiting time $1/\alpha$ for immunity loss.

## Sources

- P. Lam and O. Nguyen, "Supercriticality of the SIRS on random networks", arXiv:2604.28150 (2026), Theorems 1.1–1.3, <https://doi.org/10.48550/arXiv.2604.28150>.
