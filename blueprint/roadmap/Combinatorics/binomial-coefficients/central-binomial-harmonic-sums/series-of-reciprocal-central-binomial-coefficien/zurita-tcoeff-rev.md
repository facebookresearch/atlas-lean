# Reversed coefficients of Zurita's polynomial $T_{n-2}$

Fix a natural number $n$, let
$s_0, s_1, \dots$ be the coefficients of $S_n$ and let $c_n = s_n/2 - 1$. The rational numbers
$u_0, u_1, \dots$ are defined by $u_0 = -s_{n-1}/2 - c_n$ and
$u_{i+1} = \frac{(k + 1 - n)\, u_i + s_k/2}{k - n}$ with $k = n - 2 - i$, where the index
subtractions $n - 1$ and $n - 2 - i$ are truncated at $0$. For $n \ge 2$ they list the
coefficients of $T_{n-2}$ backwards, $t_{n-2-i} = u_i$ for $0 \le i \le n - 2$; thus
$t_{n-2} = -s_{n-1}/2 - c_n$ and $t_{k-1} = ((k + 1 - n) t_k + s_k/2)/(k - n)$ for
$k = n - 2, \dots, 1$.

## Sources

- Rimer Zurita, *Power Series Associated with Reciprocals of Generalized Central Binomial Coefficients*, INTEGERS 26 (2026), Article A2, Definition 2.
