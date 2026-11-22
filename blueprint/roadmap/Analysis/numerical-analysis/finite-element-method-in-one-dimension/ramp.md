# Clamped ramp function of a mesh element

Let $0 = x_0 < \dots < x_n = 1$ be a partition of $[0, 1]$. For $0 \le i < n$, the clamped ramp of
the $i$-th element is $r_i(x) = \max(x_i, \min(x, x_{i+1})) - x_i$: it is $0$ left of $x_i$,
$x - x_i$ on $[x_i, x_{i+1}]$ and $h_i = x_{i+1} - x_i$ right of $x_{i+1}$.
