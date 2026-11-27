# Monotone convergence theorem

Let $(X, \mathcal{M}, \mu)$ be a measure space and let $f_1 \le f_2 \le \cdots$ be measurable functions
$X \to [0, \infty]$, with pointwise limit $f = \lim_k f_k = \sup_k f_k$. Then $f$ is measurable and
$\int f \, d\mu = \lim_{k \to \infty} \int f_k \, d\mu$, the limit being taken in $[0, \infty]$.

## Idea

Integrals of increasing nonnegative functions converge to the integral of the limit, with no domination hypothesis and
with infinite values allowed. Monotonicity gives $\lim_k \int f_k \le \int f$. For the converse, a simple function
$\varphi \le f$ with finite values and a number $0 < t < 1$ give sets $\{f_k \ge t \varphi\}$ that increase to $X$, and
continuity of measures from below shows that $\lim_k \int f_k \ge t \int \varphi$. Applied to partial sums, the theorem
gives $\int \sum_n g_n \, d\mu = \sum_n \int g_n \, d\mu$ for nonnegative measurable $g_n$, and Fatou's lemma and the
dominated convergence theorem are derived from it. Nonnegativity matters: the functions $-\chi_{[k, \infty)}$ on
$\mathbb{R}$ increase to $0$, but each has integral $-\infty$.

## Statements

- [Monotone convergence theorem](monotone-convergence-integrals.md)
- [Monotone convergence theorem with suprema](lintegral-i-sup.md): the same theorem with the limits written as suprema; it does not assert that the supremum is measurable.

## Background

- [Lebesgue integral](../nonnegative-lebesgue-integral/lebesgue-integral/README.md): the integral
- [Continuity of measures from below and from above](../../measures/measures-and-countable-additivity/continuity-of-measures/README.md): used in the proof

## Sources

- S. Axler, *Measure, Integration & Real Analysis*, results 3.11 and 2.53 (version read: the open-access PDF dated 12 June 2026).
