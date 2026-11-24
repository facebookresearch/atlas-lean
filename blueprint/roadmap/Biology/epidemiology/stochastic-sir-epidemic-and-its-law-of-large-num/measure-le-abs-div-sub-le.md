# Chebyshev bound for a scaled unit Poisson increment

Let $Y$ be a unit-rate [Poisson process](../../../Probability/point-processes/poisson-processes/is-poisson-process.md) on a probability space
$(\Omega, P)$, let $N \ge 1$ be a natural number, and let $a \ge 0$ and $c > 0$ be real. Then

$$P\left(\left|\frac{Y(N a) - Y(0)}{N} - a\right| \ge c\right) \le \frac{a}{N c^2}.$$

The increment $Y(N a) - Y(0)$ is computed in $\mathbb{N}$, by truncated subtraction ($0$ when
$Y(N a) < Y(0)$); almost surely it is the true increment, since almost every path of $Y$ is
nondecreasing. It has the Poisson law of mean $N a$, hence variance $N a$, and the bound is
Chebyshev's inequality.
