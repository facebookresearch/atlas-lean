# Coefficients of Zurita's polynomial $T_{n-2}$

For natural numbers $n$ and $k$,
$t_k = u_{n-2-k}$, where $n - 2 - k$ is truncated at $0$ and $u_0, u_1, \dots$ are the reversed
coefficients of $T_{n-2}$: with $s_j$ the coefficients of $S_n$ and $c_n = s_n/2 - 1$,
$u_0 = -s_{n-1}/2 - c_n$ and $u_{i+1} = ((m + 1 - n) u_i + s_m/2)/(m - n)$ for
$m = n - 2 - i$, the indices $n - 1$ and $n - 2 - i$ being truncated at $0$. For $k \le n - 2$
these are the coefficients of $T_{n-2}(x) = \sum_{k=0}^{n-2} t_k x^k$; for $k > n - 2$,
$t_k = u_0$.

## Sources

- Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2.
