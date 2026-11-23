# Cost of the Fisher–Yates shuffle

For every vector $x$ of length $n$ and every draw
history $d$, which assigns to each position $i < n$ a number $d_i$ with $0 \le d_i < n - i$, the
Fisher–Yates computation on $x$ and $d$ has cost pair $(n, n)$: it retrieves exactly $n$ draws
and performs exactly $n$ swaps.

When $n \ge 1$, this count includes the final draw $d_{n-1} = 0$ and the self-swap at position
$n - 1$.
