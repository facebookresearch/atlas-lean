# Alzer–Richards identity for Euler numbers

Let $n \ge 1$ be an integer. For integers
$k, i \ge 0$ let $T(k, i) = 2^{-k} \sum_{j=0}^{k} \binom{k}{j} (k-2j)^i$ (with $0^0 = 1$), and
let $E_k$ be the Euler numbers: $E_k = 0$ for odd $k$, and for even $k$ they are given by
$E_0 = 1$ and $E_{2m} = -\sum_{s=0}^{m-1} \binom{2m}{2s} E_{2s}$ for $m \ge 1$. Then

$$
\sum_{k=0}^{n-1} \binom{n}{k} E_k \sum_{\nu=0}^{n+1} \binom{n+1}{\nu} T(\nu, n-k) +
(2^{n+1} - 1) E_n = \sum_{k=0}^{n} \binom{n+1}{k+1} T(k, n).
$$

With these conventions $1/\cosh x = \sum_{k \ge 0} E_k x^k / k!$.

## Sources

- Horst Alzer and Kendall C. Richards, *Extensions of Some Combinatorial Identities and Various Related Results*, INTEGERS 25 (2025), Article A61, Theorem 6.
