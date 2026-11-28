# Expected smoothness at a minimizer

Let $f=n^{-1}\sum_{i=1}^n f_i$ be the finite-sum objective of differentiable
components $f_i:\mathbb R^d\to\mathbb R$ with $n\ge 1$, and let $x^\star$ be
a fixed global minimizer of $f$ on $\mathbb R^d$. Let $v$ be a sampling
vector with law $\mathcal D$, and let $f_v$ be the weighted objective with
normalization $1/n$.

Expected smoothness at $x^\star$ means that there exists a finite real
constant $\mathcal L>0$ such that, for every fixed $x\in\mathbb R^d$, the
squared Euclidean norm on the left is integrable and

$$
\mathbb E_{\mathcal D}\!\left[\left\|\nabla f_v(x)-\nabla f_v(x^\star)\right\|_2^2\right]
\le 2\mathcal L\bigl(f(x)-f(x^\star)\bigr).
$$

Both gradients use the same draw $v$, and one constant works for all $x$.
Finiteness here is for the squared **difference**. It does not follow from
the coordinate means and does not require finite second moments of the
weights or of $\nabla f_v(x^\star)$ separately. The minimizer is of $f$,
not of the individual $f_v$.

Section 1 works with smooth components and fixes a unique global minimizer
for the analysis. The test in (7) is at the specified minimizer; it does not
include convexity or strong quasi-convexity as part of the condition.

## Depends on

- [Sampling vector](sampling-vector.md)
- [Weighted finite-sum objective](weighted-finite-sum-objective.md)
- [Expected value of a random variable](../../../Probability/foundations/laws-of-random-variables-and-identical-distribut/expectation/expectation-random-variable.md)

## Proof depends on

None beyond the statement prerequisites; this page is a definition.

## Sources

- R. M. Gower, N. Loizou, X. Qian, A. Sailanbayev, E. Shulgin, and
  P. Richtárik, [*SGD: General Analysis and Improved Rates*](https://arxiv.org/html/1901.09401v4),
  arXiv:1901.09401v4, Section 2.1, Assumption 2.1 and equation (7), in the
  setup of Sections 1 and 1.2. The separate gradient-noise assumption is in
  Section 2.2, Assumption 2.3.
