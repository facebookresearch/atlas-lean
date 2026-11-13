# Mitrinović's numbers at $a = 0$

For every complex number $b$, Mitrinović's numbers
$R^k_j(0, b)$ satisfy the following. First, for every $k \in \mathbb{N}$, $R^k_0(0, b) = 1$ if
$k = 0$ and $R^k_0(0, b) = 0$ otherwise. Second, for all $j, k \in \mathbb{N}$,
$R^{k+1}_{j+1}(0, b) = R^k_j(0, b) + (b - b(j + 1))\, R^{k+1}_j(0, b)$. Third, for all
$j, k \in \mathbb{N}$, $R^k_j(0, b) = (-b)^{j-k} c(j, k)$, where $c(j, k)$ is the unsigned
Stirling number of the first kind, which is $0$ for $k > j$, and the exponent $j - k$ is read as
$0$ when $k > j$.

The source prints the last factor of the recurrence as $R^k_{j-1}(a, b)$; it is
$R^k_{j-1}(0, b)$, the case $a = 0$ of (4.2). The source's hypothesis $b \ne 0$ is dropped: at
$b = 0$ both sides of the closed form are $\delta_{j,k}$.

## Sources

- Daniele Parisse, *On Hypersequences of an Arbitrary Sequence and Their Weighted Sums II*, INTEGERS 26 (2026), Article A36, Corollary 5.
