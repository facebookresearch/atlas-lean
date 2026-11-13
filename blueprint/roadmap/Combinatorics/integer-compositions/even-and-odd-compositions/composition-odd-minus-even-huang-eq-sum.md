# Signed count of Huang's compositions, binomial form

Let $k, n \ge 1$ and $m \ge 0$.
Among the compositions of $n + k - 1$ with exactly $m$ parts less than $k$ in which every part
less than $k$ is preceded by a part at least $k$ and followed by a part that is either the last
part or greater than $k$, let $b^{(m)}_{k,n}$ be the number with an odd number of parts minus the
number with an even number of parts. Then $b^{(m)}_{k,n}$ is the sum of
$(-1)^{\ell+j} \binom{i}{m} \binom{i+j-1}{j} \binom{m}{\ell} \binom{m+h-1}{h}$ over all
$i, j, \ell, h \ge 0$ with $i + (k+1)m + jk + \ell(k-1) + h = n$, where $\binom{-1}{0} = 1$.

## Sources

- Jia Huang, *Even and Odd Compositions with Restricted Parts*, Journal of Integer Sequences 27 (2024), Article 24.6.5, Theorem 16 (`jis-2024-24.6.5-thm-16`).
