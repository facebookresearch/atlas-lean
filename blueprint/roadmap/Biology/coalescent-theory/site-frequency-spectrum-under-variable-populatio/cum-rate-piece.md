# Cumulative rate is affine on each piece

Let $\eta$ be the [size function](size-fn.md) of a [piecewise-constant history](piecewise-history.md) with $K$ pieces, sizes $\nu_j$ and start times $s_j$. For every $j < K$ and every real $s$ with $s_j \le s$ and, if $j + 1 < K$, $s \le s_{j+1}$:

- $1/\eta$ is integrable on the interval between $0$ and $s$, and
- the [cumulative rate](cum-rate.md) is affine there: $R_\eta(s) = R_\eta(s_j) + (s - s_j)/\nu_j$.
