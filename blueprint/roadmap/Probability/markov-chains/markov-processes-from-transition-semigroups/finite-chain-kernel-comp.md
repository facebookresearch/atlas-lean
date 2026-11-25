# Composition rule for finite-chain kernels

Let $(K_t)_{t \ge 0}$ be Markov kernels on a measurable space $E$ satisfying the Chapman–Kolmogorov
equations $K_{s+t}(x, A) = \int K_s(x, dy)\, K_t(y, A)$, and let $F_{s, \mathbf t}$ be the
[finite-dimensional kernel](finite-chain-kernel.md) at times $\mathbf t = (t_0, \dots, t_{n-1})$
from time $s$. If $s \le u$ and $u \le t_i$ for every $i$, then for every $x \in E$ and
measurable $B \subseteq E^n$

$$\int_E K_{u - s}(x, dy)\, F_{u, \mathbf t}(y, B) = F_{s, \mathbf t}(x, B):$$

moving the starting time forward from $s$ to $u$ and then evolving to the requested times gives
the same law as evolving there directly.
