# Hankel determinants of the Eulerian polynomials

For $m \ge 0$ let $P_m \in \mathbb{Z}[X]$
be the Eulerian polynomial $P_m = \sum_{k=0}^{m} W_{m,k} X^k$, where
$W_{m,k} = \sum_{i=0}^{m-k} (-1)^i \binom{m+1}{i} (m-k-i)^m$ with $0^0 = 1$ (so $P_0 = 1$ and
$P_2 = 1 + X$). Then for every $n \ge 0$ the Hankel determinant
$\det(P_{i+j})_{0 \le i, j \le n}$ equals $X^{\binom{n+1}{2}} \prod_{k=1}^{n} (k!)^2$.

The proof writes $P_m$ as the moments of a weighted Motzkin table with down-step weights
$\lambda_k = k^2 X$ (Barry's Eulerian moment recurrence) and applies the weighted-Motzkin
determinant theorem.

## Sources

- Paul Barry, "Eulerian Polynomials as Moments, via Exponential Riordan Arrays," Journal of Integer Sequences 14 (2011), Article 11.9.5, corollary lines 240–243, <https://cs.uwaterloo.ca/journals/JIS/VOL14/Barry7/barry172.tex>. Eulerian closed form `W_{n,k}` at lines 93–94.
