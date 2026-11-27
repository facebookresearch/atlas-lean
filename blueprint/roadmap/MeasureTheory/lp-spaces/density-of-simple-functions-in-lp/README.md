# Density of simple functions in L^p

Let $(X, \mathcal{M}, \mu)$ be a measure space and $0 < p \le \infty$. For every measurable function $f$ on $X$, real or
complex, with $\|f\|_p < \infty$, and every $\varepsilon > 0$, there is a measurable function $g$ with finitely many
values such that $\|g\|_p < \infty$ and $\|f - g\|_p < \varepsilon$: simple functions are dense in $\mathcal{L}^p(\mu)$.
For $p < \infty$ these simple functions are the combinations $\sum_j a_j \chi_{E_j}$ of indicators of measurable sets of
finite measure, so for $1 \le p < \infty$ such combinations are dense in $L^p(\mu)$.

## Idea

For $p < \infty$, approximate the positive and negative parts of the real and imaginary parts of $f$ from below by
simple functions: the approximations converge to $f$ pointwise and are dominated by $2|f|$, so the dominated convergence
theorem gives $\|f - g\|_p \to 0$, even for $p < 1$, where $\|\cdot\|_p$ is not a norm. By Markov's inequality, for
$p < \infty$ a simple function with $\|g\|_p < \infty$ vanishes outside a set of finite measure. For $p = \infty$,
change $f$ on a null set to make it bounded; the same approximations then converge uniformly. Simple functions in
$\mathcal{L}^\infty$ may be nonzero on a set of infinite measure, like the constant $1$ on $\mathbb{R}$. Density of
simple functions is the usual first step in extending a statement from indicators of sets to all of $L^p$.

## Statements

- [Simple functions are dense in $L^p$](lp-simple-functions-dense.md)

## Background

- [L^p spaces](../normed-and-ordered-structure-of-lp-spaces/lp-space-of-a-measure/README.md): the space $L^p$
- [Approximation by simple functions](../../integration/approximation-by-simple-functions/README.md): used in the proof

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, Exercise 17 in Section 7A (version read: the open-access PDF dated 12 June 2026).
