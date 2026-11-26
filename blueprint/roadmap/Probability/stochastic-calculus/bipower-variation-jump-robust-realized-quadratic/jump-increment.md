# Increment of a pure-jump path over a grid cell

For a finite set $s$ of jump indices with jump times $\tau_k$ and sizes $\xi_k$, and $n, i \in \mathbb{N}$, the jump increment is the increment $J((i+1)/n) - J(i/n)$ of the pure-jump path $J(t) = \sum_{k \in s} \xi_k \mathbf 1\{\tau_k \le t\}$ over the $i$-th cell $(i/n, (i+1)/n]$ of the grid of mesh $1/n$. For $n = 0$ both endpoints are $0$ by the convention for division by zero, so the increment is $0$.
