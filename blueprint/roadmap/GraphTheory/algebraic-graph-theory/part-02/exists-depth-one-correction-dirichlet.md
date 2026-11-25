# Integral Dirichlet problem on chains with a correction at depth one

Let $\iota$ be an index set and, for each $i \in \iota$, let $n_i \ge 1$ be a natural number, the length of a chain with vertices $0, 1, \dots, n_i$, and $r_i : \mathbb{N} \to \mathbb{Z}$. Then there are integers $\nu_i$ and $c_i(d)$, for $i \in \iota$ and $d \in \mathbb{N}$, such that

- $\nu_i = 0$ whenever $n_i = 1$;
- $c_i(0) = 0$ and $c_i(d) = 0$ for every $d \ge n_i$;
- at every interior vertex $d$ of chain $i$, that is, for $1 \le d \le n_i - 1$, the discrete Laplacian of $c_i$ satisfies

$$c_i(d-1) - 2\,c_i(d) + c_i(d+1) = \begin{cases} -(r_i(1) - \nu_i) & \text{if } d = 1, \\ -r_i(d) & \text{if } d \ge 2. \end{cases}$$

So the Dirichlet problem $\Delta c_i = -r_i$ with zero boundary values on each chain has an integer solution once the right-hand side is corrected by $\nu_i$ at the first interior vertex; chains of length one have no interior vertex and take $\nu_i = 0$. Without the correction an integer solution need not exist: for $n_i = 2$ and $r_i(1) = 1$ the equation at $d = 1$ reads $-2\,c_i(1) = -1$.
