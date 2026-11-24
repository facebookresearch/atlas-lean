# Folded site frequency spectrum

Let $n$ be a natural number and $\xi_j$ ($j \in \mathbb{N}$) real functions on a set $\Omega$, the
unfolded counts. For a natural number $i$, the folded count is the function

$$\eta_i = \begin{cases} \xi_i & \text{if } 2i = n, \\ \xi_i + \xi_{n-i} & \text{otherwise,}
\end{cases}$$

where $n - i$ is truncated subtraction ($0$ when $i \ge n$). For $1 \le i \le n/2$ this is the
folded site frequency spectrum (Fu 1995), used when the ancestral allele is unknown:
$\eta_i = \xi_i + \xi_{n-i}$ for $2i < n$, and $\eta_{n/2} = \xi_{n/2}$ for even $n$. Outside
that range the formula still applies: $\eta_i = \eta_{n-i}$ for $n/2 < i < n$,
$\eta_0 = \xi_0 + \xi_n$ for $n \ge 1$, and $\eta_i = \xi_i + \xi_0$ for $i \ge n$, $i \ge 1$.
