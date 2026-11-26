# Blocks of a Boolean function on n + k variables

Let $n$ and $k$ be natural numbers. For a Boolean function $F$ on $\{0,1\}^{n+k}$ and a natural number $i$, the $i$-th block of $F$ is the Boolean function on $\{0,1\}^n$

$$F_i(x) = F(x_0, \dots, x_{n-1}, \beta_0(i), \dots, \beta_{k-1}(i)),$$

where $\beta_j(i) \in \{0, 1\}$ is bit $j$ of $i$, the coefficient of $2^j$ in the binary expansion of $i$. The block is defined for every natural number $i$; only the bits $0, \dots, k-1$ of $i$ are used.
