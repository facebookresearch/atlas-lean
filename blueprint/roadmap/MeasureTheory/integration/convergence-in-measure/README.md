# Convergence in measure is metrizable

For Borel measurable functions $g, h : \mathbb{R} \to \mathbb{R}$ put

$$d(g, h) = \int_{[0,1]} \frac{|g(x) - h(x)|}{1 + |g(x) - h(x)|}\, dx,$$

with respect to Lebesgue measure. Then for Borel measurable $f, f_0, f_1, \ldots$ one has
$d(f_n, f) \to 0$ if and only if $f_n \to f$ in Lebesgue measure on $[0, 1]$: for every
$\varepsilon > 0$ the measure of $\{x \in [0,1] : |f_n(x) - f(x)| \ge \varepsilon\}$ tends to $0$.
On functions $d$ is a pseudometric; on almost-everywhere classes it is the metric of
$L^0([0, 1])$.

## Idea

Convergence in measure ignores how large a function is on a small set, so no norm describes it;
the bounded transform $t \mapsto t / (1 + t)$ truncates large deviations and gives a metric
instead. If $d(f_n, f)$ is small, then by Markov's inequality the set where
$|f_n - f| \ge \varepsilon$ has small measure, since $t/(1+t)$ is increasing; conversely, if that
set is small, splitting the integral into it and its complement makes $d(f_n, f)$ small.

## Statements

- [Convergence in the $L^0$ pseudometric is convergence in measure](tendsto-l0-pseudo-metric-zero-iff-tendst.md)
- [The $L^0$ pseudometric on $[0,1]$](l0-pseudo-metric.md): the metric of the statement.
- [Measurable functions representing $L^0([0,1])$](l0-unit-interval.md): the functions it is defined on.
