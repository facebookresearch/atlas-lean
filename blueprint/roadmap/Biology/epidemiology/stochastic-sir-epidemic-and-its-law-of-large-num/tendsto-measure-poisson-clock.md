# Uniform law of large numbers for unit Poisson clocks

Let $(\Omega, P)$ be a probability space and, for each natural number $N$, let $Y_N$ be a
unit-rate [Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) on it; no relation between the processes for
different $N$ is assumed. Then for every real $B$ and every $\eta > 0$,

$$P\left(\exists\, a \in [0, B],\ |Y_N(N a)/N - a| > \eta\right) \to 0 \quad (N \to \infty).$$

The event is $\{\sup_{a \in [0, B]} |Y_N(N a)/N - a| > \eta\}$; it is not assumed measurable, and
$P$ is applied to it as an outer measure.
