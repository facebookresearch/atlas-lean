# Finite-time $L^p$ blow-up of the reaction-diffusion Trojan Y-chromosome model

**Model.** Let $\Omega \subset \mathbb{R}^n$ be a bounded domain with outward normal $n$. Let $f$, $m$, $s$ be the densities of wild-type XX females, wild-type XY males and released YY supermales. With birth rate $\beta \ge 0$, death rate $\delta \ge 0$, carrying capacity $K > 0$, supermale release rate $\mu \ge 0$ and logistic factor $L = 1 - (f + m + s)/K$,

$$\partial_t f = \Delta f + \tfrac12 \beta L f m - \delta f, \qquad \partial_t m = \Delta m + \tfrac12 \beta L f m + \beta L f s - \delta m, \qquad \partial_t s = \Delta s + \mu - \delta s,$$

on $\Omega \times (0,\infty)$ with homogeneous Neumann conditions $\nabla f \cdot n = \nabla m \cdot n = \nabla s \cdot n = 0$ on $\partial\Omega$ and positive initial data $(f(\cdot,0), m(\cdot,0), s(\cdot,0))$.

**Theorem 3.1 (blow-up without releases).** If $\mu = 0$, there exist positive initial data for which the solution blows up in finite time:

$$\limsup_{t \to T^{*}} \|f(\cdot,t)\|_{L^p(\Omega)} = +\infty \quad\text{and}\quad \limsup_{t \to T^{**}} \|m(\cdot,t)\|_{L^p(\Omega)} = \infty$$

for some finite $T^{*}$, $T^{**}$ and every $p \ge 1$.

**Theorem 3.2 (blow-up driven by releases).** If $\mu > 0$, then for every positive initial datum there is a threshold $\mu^{*}$ such that for every $\mu > \mu^{*}$ the solution blows up in finite time in the same sense, for every $p \ge 1$.

**Corollaries 1 and 2.** The same two statements hold for the original four-compartment spatial model that also tracks released YY females $r$ (with $\partial_t r = \Delta r + \mu - \delta r$ and supermales produced by matings with $r$).

The thresholds obtained in the proofs are not claimed to be sharp; numerical experiments in the source suggest that much smaller initial data or release rates already give negative male densities or blow-up.

## Expansion

The mechanism is inherited from the spatially homogeneous system. The reaction term of the male equation at $m = 0$ is $\beta f s\,(1 - (f+s)/K)$, which is negative once $f + s > K$, so the quasi-positivity condition for invariance of the nonnegative cone fails and $m$ can become negative on a time interval $[T_1, T_2]$. Writing $m = -\tilde m$ with $\delta_1 < \tilde m < \delta_2$ there and integrating the female equation over $\Omega$ (the Laplacian integrates to zero under Neumann conditions), the term $\tfrac{\beta}{2K} f^2 \tilde m$ dominates. With $F(t) = \int_\Omega f\,dx$ and Jensen's or Hölder's inequality this gives a Riccati-type inequality

$$F'(t) \ge c_1 F(t)^2 - c_2 F(t), \qquad c_1, c_2 > 0,$$

so $F$, the $L^1$ norm of $f$, blows up in finite time once $F(0)$ exceeds an explicit threshold; since $\Omega$ is bounded, the $L^p$ norms for $p \ge 1$ blow up too. With releases, $s$ approaches $\mu/\delta$, and the extra positive contribution $\tfrac{\beta}{2K} f \tilde m s$ supplies the required growth once $\mu$ is large, independently of the size of the initial data.

The result shows that the well-posedness defect of the classical Trojan Y-chromosome model is not a lumped-model artifact: diffusion alone does not restore positivity, so any eradication analysis built on this model presupposes positivity that is not guaranteed.

## Sources

- R. D. Parshad, M. A. Beauregard, E. M. Takyi, T. Griffin and L. Bobo, "Large and small data blow-up solutions in the Trojan Y chromosome model" (2019), Section 3 (Theorems 3.1 and 3.2, Corollaries 1 and 2), with the ODE precursors in Section 2 (Lemma 2.2 and Theorems 2.3 and 2.4), <https://doi.org/10.48550/arXiv.1907.06079>.
