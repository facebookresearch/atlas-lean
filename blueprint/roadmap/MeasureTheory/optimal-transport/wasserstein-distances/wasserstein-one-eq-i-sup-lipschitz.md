# Kantorovich–Rubinstein formula

Let $X$ be a Polish metric space and let $\mu, \nu$ be Borel probability measures on $X$ with finite
first moments, $\int d(x_0, x) \, d\mu(x) < \infty$ and $\int d(x_0, x) \, d\nu(x) < \infty$ for some
$x_0 \in X$. Then

$$W_1(\mu, \nu) = \sup_{\|\psi\|_{\mathrm{Lip}} \le 1} \Bigl( \int_X \psi \, d\mu - \int_X \psi \, d\nu \Bigr),$$

the supremum over all $1$-Lipschitz functions $\psi : X \to \mathbb{R}$.

The inequality $\ge$ is elementary and is [proved for nonnegative Lipschitz functions](lintegral-le-add-mul-wasserstein-one.md).

## Informally uses

- [Kantorovich duality for lower semicontinuous costs](../kantorovich-duality/kantorovich-duality-lsc.md):
  Villani derives the formula from Theorem 5.10(i) applied to the cost $c = d$.

## Sources

- C. Villani, *Optimal Transport: Old and New*, Grundlehren der mathematischen Wissenschaften 338, Springer 2009, Remark 6.5, formula (6.3), from Theorem 5.10(i) and Particular Case 5.4 (for $c = d$, the $c$-convex functions are the $1$-Lipschitz functions).
