# Skorokhod representation on the real line

Let $F_n$, $1 \le n \le \infty$, be distribution functions on $\mathbb R$ such that $F_n \Rightarrow F_\infty$,
that is, $F_n(y) \to F_\infty(y)$ at every point $y$ where $F_\infty$ is continuous. Then there are random variables
$Y_n$, $1 \le n \le \infty$, defined on one probability space, such that $Y_n$ has distribution function $F_n$ for
every $n$ and $Y_n \to Y_\infty$ almost surely.

## Proof

Take $\Omega = (0, 1)$ with its Borel sets and Lebesgue measure, and $Y_n(x) = \sup\{y : F_n(y) < x\}$. This is the
quantile function of the probability measure whose distribution function is $F_n$, so $Y_n$ has distribution function
$F_n$. The levels $x$ at which $F_\infty$ is constant on a nondegenerate open interval are countable, since these
intervals are disjoint and each contains a rational. At any other $x \in (0, 1)$, comparing $F_n$ with $F_\infty$ at
continuity points of $F_\infty$ slightly below and slightly above $Y_\infty(x)$ shows $\liminf_n Y_n(x) \ge Y_\infty(x)$
and $\limsup_n Y_n(x) \le Y_\infty(x)$; such points exist because the continuity points of a distribution function are
dense. So $Y_n \to Y_\infty$ outside a countable set $\{x_1, x_2, \dots\}$, which has Lebesgue measure zero: for
$\varepsilon > 0$ it is covered by open intervals of lengths $\varepsilon 2^{-k}$, $k \ge 1$.

## Depends on

- [Distribution function](../helly-s-selection-theorem/is-distribution-function.md)
- [Probability measure](../../foundations/probability-measures/is-probability-measure.md)

## Proof depends on

- [Construction of measures on ℝ](../../foundations/probability-measures-from-distribution-functions/stieltjes-measure-construction.md)
- [Inverse transform sampling](../../distributions/distribution-functions/quantile-function-and-inverse-transform-sampling/inverse-transform-sampling/map-cdf-quantile-restrict-icc.md)
- [The continuity points of the cdf are dense](../../distributions/distribution-functions/cumulative-distribution-function/dense-cdf-continuity-points.md)
- [Lebesgue measure on the real line](../../../MeasureTheory/lebesgue-measure/lebesgue-measure-on-euclidean-spaces/lebesgue-measure-on-the-real-line/lebesgue-measure.md)

## Sources

- R. Durrett, *Probability: Theory and Examples*, 5th ed., Section 3.2 (weak convergence of distribution functions) and Theorem 3.2.8 (version read: the author's January 2019 PDF).
