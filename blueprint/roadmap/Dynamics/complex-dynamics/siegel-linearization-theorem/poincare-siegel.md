# Poincaré–Siegel linearisation theorem

Let $\alpha$ be a Diophantine real number and let
$\lambda = e^{2\pi i \alpha}$. If $f : \mathbb{C} \to \mathbb{C}$ is analytic at $0$ with
$f(0) = 0$ and $f'(0) = \lambda$, then there is a function $u : \mathbb{C} \to \mathbb{C}$,
analytic at $0$ with $u(0) = 0$ and $u'(0) = 1$, such that $f(u(z)) = u(\lambda z)$ for all $z$
in some neighbourhood of $0$.

## Sources

- Carl Ludwig Siegel, *Iteration of analytic functions*, Ann. of Math. (2) 43 (1942), 607–612.
- Henri Poincaré, doctoral thesis (Paris, 1879): the earlier formal-power-series version.
- Oliver Knill, *Some Fundamental Theorems in Mathematics* (2023), §83 (KAM; the Poincaré–Siegel theorem is
  discussed after the theorem of the section), <https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf>.
- Problem `poincare_siegel_linearisation` of the lean-eval benchmark.
