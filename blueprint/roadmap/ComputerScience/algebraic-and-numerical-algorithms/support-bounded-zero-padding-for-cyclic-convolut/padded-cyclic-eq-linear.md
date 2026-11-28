# Zero padding to the full support makes cyclic convolution linear

Let $M, K \ge 1$ and $N \ge M + K - 1$ be natural numbers, and let $x$ and $y$ be signals of lengths $M$ and $K$, with [zero extensions](zero-extend.md) $x^{(N)}$ and $y^{(N)}$ to length $N$. Then for every natural number $t < M + K - 1$,

$$\bigl(x^{(N)} \circledast y^{(N)}\bigr)(t \bmod N) = (x * y)(t),$$

where $\circledast$ is [cyclic convolution](cyclic-convolution.md) on $\mathbb{Z}/N\mathbb{Z}$ and $*$ is [linear convolution](linear-convolution.md). So the cyclic coefficients at the classes of $0, \ldots, M + K - 2$ are the linear coefficients there. Padding to $M + K - 2$ is not enough when $M, K \ge 2$ ([aliasing](one-short-padding-aliases.md)); the [dyadic case](padded-cyclic-eq-linear-dyadic.md) and the [two-dimensional version](padded-cyclic-eq-linear-two-dim.md) follow the same bound.
