# First Bernoulli formula for the inverse of Zagier's matrix

For a natural number $K$,
$P_K$ is the rational matrix with rows and columns indexed by $1 \le i, j \le K - 1$ (empty
when $K \le 1$) whose $(i, j)$ entry is

$$(P_K)_{ij} = \frac{2}{2i-1} \sum_{n=0}^{2K-2i} \binom{2j-1}{2K-2i-n+1} \binom{n+2i-2}{n} B_n,$$

where $B_n$ is the $n$-th Bernoulli number with $B_1 = -\frac{1}{2}$ and $\binom{m}{k} = 0$
for $k > m$.
