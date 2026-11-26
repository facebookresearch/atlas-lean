# Cumulative binary digit sums via the Takagi function

For a natural number $m$, write
$s_1(m)$ for the sum of the binary digits of $m$ and $S_1(m) = \sum_{i=0}^{m-1} s_1(i)$. Let
$k$ and $r$ be natural numbers with $r < 2^k$, and put $n = 2^k + r$ and $x = r / 2^k$. Write
$\tau(x)$ for the Takagi value of the dyadic presentation $r / 2^k$, and $\delta(n)$ for the
number of $D$-nodes of the divide-and-conquer tree on $n$ leaves, given by $\delta(1) = 0$,
$\delta(2m) = 2 \delta(m)$ and $\delta(2m + 1) = \delta(m) + \delta(m + 1) + 1$ for $m \ge 1$.
Then $S_1(n) = (nk + 2^k (2x - \tau(x)))/2$, $S_1(n) = (nk + 2r - 2^k \tau(x))/2$ and
$S_1(n) = (nk + 2r - \delta(n))/2$.

## Sources

- Laura Monroe, *Takagi Function Identities on Dyadic Rationals*, Journal of Integer Sequences 27 (2024), Article 24.2.7, Corollary 31 (`jis-2024-24.2.7-cor-31`).
