# Transit time and mean age at equilibrium

**Compartmental system.** Mass in $d$ pools obeys $\dot x = Bx + s$ with input $0 \ne s \in [0,\infty)^d$ and a matrix $B$ with $b_{ii} < 0$, $b_{ij} \ge 0$ ($i \ne j$, rate of transfer from pool $j$ to pool $i$) and column sums $\sum_i b_{ij} \le 0$ (the deficit is the loss rate from pool $j$). Assume all eigenvalues of $B$ have negative real part, so $x^\ast = -B^{-1}s$ is the exponentially stable equilibrium.

**Proposition.** Let $r_i$ be the mean remaining time in the system of a particle that has just entered pool $i$, $\beta = s/(\mathbf 1^\top s)$ the distribution of external inputs over pools and $\eta = x^\ast/(\mathbf 1^\top x^\ast)$ the equilibrium distribution of mass. Then

$$r^\top = -\mathbf 1^\top B^{-1}, \qquad R = -\mathbf 1^\top B^{-1}\beta, \qquad M = -\mathbf 1^\top B^{-1}\eta,$$

where $R$ is the mean transit time of the system (mean age of particles at exit) and $M$ the mean age of the particles present at equilibrium. Moreover $R$ equals the turnover time $\mathbf 1^\top x^\ast / \mathbf 1^\top s$, while in general $M \neq R$: both are convex combinations of the $r_i$, weighted by inputs and by stocks respectively.

## Depends on

- [Mean age system of a nonautonomous compartmental system](mean-age-system-of-a-nonautonomous-compartmental-system.md)

## Expansion

A particle in pool $i$ stays for an exponential time with mean $-1/b_{ii}$ and then moves to pool $j$ with probability $p_{ij} = -b_{ji}/b_{ii}$ or leaves. First-step analysis gives $r_i = -1/b_{ii} + \sum_{j \ne i} p_{ij} r_j$; multiplying by $-b_{ii}$ gives $B^\top r + \mathbf 1 = 0$, so $r^\top = -\mathbf 1^\top B^{-1}$, and averaging over entry pools gives $R$. Since $x^\ast = -B^{-1}s$, $R = \mathbf 1^\top x^\ast / \mathbf 1^\top s$, the stock-over-flux turnover time. The mean age formula is the stationary solution of the mean age system. For $B = \begin{pmatrix} -1 & 2 \\ 0.5 & -2 \end{pmatrix}$ with input into pool $1$ (outflow only from pool $1$) one gets $r_1 < r_2$ and hence $R = r_1 < M$, whereas for $B = \begin{pmatrix} -1 & 1 \\ 1 & -2 \end{pmatrix}$ (outflow only from pool $2$) $r_1 > r_2$ and $R > M$. In pharmacokinetics $R$ is the mean residence time of a dose administered into the input pools.

## Sources

- M. Rasmussen, A. Hastings, M. J. Smith, F. B. Agusto, B. M. Chen-Charpentier, F. M. Hoffman, J. Jiang, K. E. O. Todd-Brown, Y. Wang, Y.-P. Wang and Y. Luo, "Transit times and mean ages for nonautonomous and autonomous compartmental systems", Journal of Mathematical Biology 73 (2016), 1379–1398, Section 2 (Eqs. (1)–(5), Example 1), <https://doi.org/10.1007/s00285-016-0990-8>, PMCID: PMC5061853.
