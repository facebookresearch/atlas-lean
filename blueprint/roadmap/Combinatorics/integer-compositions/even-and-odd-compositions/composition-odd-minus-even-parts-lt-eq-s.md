# Signed count of compositions with exactly $m$ parts less than $k$

Let $k, n \ge 1$ and
$m \ge 0$. Among the compositions of $n + k - 1$ with exactly $m$ parts less than $k$, the number
with an odd number of parts minus the number with an even number of parts is the sum of
$(-1)^{i+\ell+1} \binom{i+j-1}{j} \binom{i}{m} \binom{m}{\ell}$ over all $i, j, \ell \ge 0$ with
$i + j + (k-1)(\ell + i - m - 1) = n$, where $\binom{-1}{0} = 1$.

Only finitely many terms are nonzero: a nonzero term has $\ell \le m$ and
$i, j \le n + (k-1)(m+1)$.

## Sources

- Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal of Integer Sequences 27 (2024), Article 24.6.5, Theorem 17 (`jis-2024-24.6.5-thm-17`).
