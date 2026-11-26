# Eigenstructure of the K-population genotype covariance matrix

Consider $M = \sum_{k=1}^K M(k)$ diploid samples partitioned into $K$ populations of sizes $M(k) \ge 1$,
with an ancestral allele frequency $P \in (0, 1)$ and population allele frequencies $p_1, \dots, p_K$
having drift covariance $\operatorname{Cov}(p_a, p_b \mid P) = P(1 - P) B_{ab}$ and within-population
drift $\tau_k = B_{kk}$ under Hardy–Weinberg equilibrium in each population.
Let $C_j \in \{0, 1, 2\}$ be the allele count of sample $j$, let $C_j^* = C_j - \bar C$ be the
sample-centered genotype vector, let $V^* = \operatorname{Cov}(C^* \mid P)$, and set
$R^* = V^* / (2 P (1 - P))$.

Conditional on the ancestral allele frequency $P$:
1. $R^*$ does not depend on $P$.
2. $R^*$ has eigenvalue $0$ with eigenvector $\mathbf{1} = (1, \dots, 1)^\top$.
3. For each population $k \in \{1, \dots, K\}$, $R^*$ has $M(k) - 1$ small eigenvalues equal to $1 - \tau_k$ (supported on vectors summing to $0$ within population $k$).
4. $R^*$ has $K - 1$ population-structure eigenvectors spanning the $(K - 1)$-dimensional subspace of population-constant vectors orthogonal to $\mathbf{1}$. When $B$ has rank $K$ and every $M(k) \to \infty$, these $K - 1$ eigenvalues diverge with $M$.

## Expansion

Decompose $\mathbb{R}^M$ into the $K$-dimensional subspace $F$ of population-indicator vectors
(with orthonormal basis $f^{[k]}$ supported on population $k$) and its orthogonal complement
$F^\perp$. On $F^\perp$, genotype covariance within population $k$ is purely binomial variance
$2 p_k(1 - p_k)$ whose conditional expectation given $P$ is $2P(1 - P)(1 - \tau_k)$, yielding
the $M(k) - 1$ eigenvalues $1 - \tau_k$. On $F$, centering projects onto $F^* = F \cap \mathbf{1}^\perp$,
leaving $\mathbf{1}$ in the kernel and $K - 1$ eigenvectors determined by $T D B D T$ where
$D_{kk} = \sqrt{M(k)}$ and $T = I - \frac{1}{M}\mathbf{1}\mathbf{1}^\top$.

## Sources

- N. Patterson, A. L. Price, and D. Reich, "Population Structure and Eigenanalysis", PLOS Genetics 2 (2006), e190, <https://doi.org/10.1371/journal.pgen.0020190> (PMC1713260). (Theorem 3.)
