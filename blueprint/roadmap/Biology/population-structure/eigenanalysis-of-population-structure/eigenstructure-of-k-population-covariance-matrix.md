# Eigenstructure of the K-population genotype covariance matrix

Consider $M = \sum_{k=1}^K M(k)$ diploid samples partitioned into $K$ populations of sizes $M(k) \ge 1$,
sample $j$ belonging to population $k(j)$. Fix an ancestral allele frequency $P \in (0, 1)$. The population
allele frequencies $\mathbf p = (p_1, \dots, p_K) \in [0, 1]^K$ are random with

$$\mathbb{E}[p_k \mid P] = P, \qquad \operatorname{Cov}(p_a, p_b \mid P) = P(1 - P)\, B_{ab},$$

for a fixed symmetric positive semidefinite $K \times K$ matrix $B$ not depending on $P$; put
$\tau_k = B_{kk}$, which lies in $[0, 1]$ because $p_k \in [0, 1]$. Conditionally on $\mathbf p$, the allele
counts $C_1, \dots, C_M$ are independent with $C_j \sim \operatorname{Binomial}(2, p_{k(j)})$ (Hardy–Weinberg
equilibrium within each population). Let $\bar C = \frac1M \sum_j C_j$, let $C^* = C - \bar C\,\mathbf 1$ be the
sample-centred genotype vector, let $V^* = \operatorname{Cov}(C^* \mid P)$, and set
$R^* = V^* / (2 P (1 - P))$.

Write $u = (\sqrt{M(1)}, \dots, \sqrt{M(K)})^\top$, $D = \operatorname{diag}(u)$ and
$T = I_K - u u^\top / M$, let $f^{[k]} = M(k)^{-1/2}\, \mathbf 1_{\{j : k(j) = k\}}$, which form an
orthonormal basis of the space $F$ of vectors constant on each population, and set

$$S = T \bigl[\operatorname{diag}(1 - \tau_1, \dots, 1 - \tau_K) + 2 D B D\bigr] T.$$

Then:

1. $R^*$ does not depend on $P$.
2. $R^* \mathbf 1 = 0$.
3. For each population $k$, every vector supported on population $k$ whose coordinates sum to $0$ is an
   eigenvector of $R^*$ with eigenvalue $1 - \tau_k$; these give $M(k) - 1$ eigenvalues $1 - \tau_k$.
4. $F$ is invariant under $R^*$, and in the basis $f^{[1]}, \dots, f^{[K]}$ the restriction of $R^*$ to $F$ is
   $S$. So $R^*$ has $K - 1$ further eigenvectors, spanning $F \cap \mathbf 1^\perp$, whose eigenvalues are
   those of $S$ on $u^\perp$.
5. If $B$ is positive definite, each of these $K - 1$ eigenvalues is at least
   $2 \lambda_{\min}(B) \min_k M(k)$, so all of them tend to infinity as every $M(k) \to \infty$
   (a lower bound derived from the source's Eq. (33) for $S$, rather than printed verbatim in Theorem 3).

## Expansion

1. By the law of total covariance,
   $\operatorname{Cov}(C \mid P) = \mathbb{E}[\operatorname{Cov}(C \mid \mathbf p) \mid P] + \operatorname{Cov}(\mathbb{E}[C \mid \mathbf p] \mid P)$.
   The first term is diagonal with entries $\mathbb{E}[2p_{k(j)}(1 - p_{k(j)}) \mid P] = 2P(1 - P)(1 - \tau_{k(j)})$,
   and the second is $4P(1 - P) Z B Z^\top$, where $Z$ is the $M \times K$ population-indicator matrix. With
   $H = I_M - \mathbf 1 \mathbf 1^\top / M$, this gives
   $R^* = H \bigl[\operatorname{diag}(1 - \tau_{k(j)}) + 2 Z B Z^\top\bigr] H$, which proves 1 and 2.
2. A vector $x$ supported on population $k$ with coordinate sum $0$ satisfies $Hx = x$ and $Z^\top x = 0$, so
   $R^* x = (1 - \tau_k) x$, which proves 3. These vectors span $F^\perp$, so $F$ is invariant.
3. With $U = Z D^{-1}$, whose columns are the $f^{[k]}$, one has $\mathbf 1 = U u$, $HU = UT$,
   $U^\top \operatorname{diag}(1 - \tau_{k(j)}) U = \operatorname{diag}(1 - \tau_k)$ and $U^\top Z = D$, which
   gives $S$ in 4. Since $T$ is the orthogonal projection onto $u^\perp$, on $u^\perp$ the quadratic
   form of $S$ is at least $2 x^\top D B D x \ge 2 \lambda_{\min}(B) \min_k M(k) \|x\|^2$, which
   proves 5.

## Sources

- N. Patterson, A. L. Price, and D. Reich, "Population Structure and Eigenanalysis", PLOS Genetics 2 (2006), e190, <https://doi.org/10.1371/journal.pgen.0020190> (PMC1713260). (Theorem 3 and its proof; item 5's explicit lower bound is derived from Eq. (33).)
