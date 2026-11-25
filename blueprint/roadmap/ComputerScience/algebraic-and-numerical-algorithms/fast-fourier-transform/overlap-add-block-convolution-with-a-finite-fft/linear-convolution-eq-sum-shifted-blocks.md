# Overlap-add decomposition of linear convolution

Let $x$ be a signal of length $N$, $h$ a filter of length $M$ and $L \ge 1$ a block length. Split $x$ into $B = \lceil N/L \rceil$ blocks $x^{(b)}$ of length $L$, with $x^{(b)}_i = x_{bL + i}$ (zero past the end of $x$). Then for every $n$,

$$(x * h)_n = \sum_{b < B,\ bL \le n} (x^{(b)} * h)_{n - bL},$$

where $*$ is full linear convolution, $(u * v)_t = \sum_{j \le t} u_j v_{t-j}$ with signals extended by zero.
