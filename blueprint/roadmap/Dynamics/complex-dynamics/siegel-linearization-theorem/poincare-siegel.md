# Poincaré–Siegel linearisation theorem

Let $\alpha$ be a Diophantine real number and let
$\lambda = e^{2\pi i \alpha}$. If $f : \mathbb{C} \to \mathbb{C}$ is analytic at $0$ with
$f(0) = 0$ and $f'(0) = \lambda$, then there is a function $u : \mathbb{C} \to \mathbb{C}$,
analytic at $0$ with $u(0) = 0$ and $u'(0) = 1$, such that $f(u(z)) = u(\lambda z)$ for all $z$
in some neighbourhood of $0$.

## Sources

- C. L. Siegel, *Iteration of analytic functions*, Annals of Math. 43 (1942), 607-612. Earlier formal-power-series version: H. Poincaré thèse (1879). Listed as §83 (additional statement 1) in O. Knill, *Some Fundamental Theorems in Mathematics* (https://people.math.harvard.edu/~knill/graphgeometry/papers/fundamental.pdf). Problem `poincare_siegel_linearisation` of the lean-eval benchmark.
