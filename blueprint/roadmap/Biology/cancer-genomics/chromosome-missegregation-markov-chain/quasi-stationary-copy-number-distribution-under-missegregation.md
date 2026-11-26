# Quasi-stationary copy-number distribution under chromosome missegregation

**Model.** Follow one chromosome type along a random lineage of a clonally expanding population in which every viable cell divides each generation. A cell with $i \in \{1, \dots, N\}$ copies gives a random daughter $i - 1$, $i$ or $i + 1$ copies with probabilities $ip/2$, $1 - ip$ and $ip/2$ (each copy missegregates independently with probability $p$, to first order in $p$). Cells with $0$ or more than $N$ copies are dead, an absorbing state. Assume $0 < p < 1/N$. The transition matrix on the viable states is

$$M = I + pJ, \qquad J_{ii} = -i, \quad J_{i, i \pm 1} = \frac{i}{2}, \quad J_{ij} = 0 \ \ (|i - j| \ge 2),$$

and $(M^g)_{ij}$ is the fraction, among $2^g$ potential descendants after $g$ generations of a founder with $i$ copies, of viable cells with $j$ copies.

**Theorem.** The limiting distribution of the copy number conditional on viability (the quasi-stationary distribution of $M$) does not depend on the founder karyotype or on $p$, and equals $v = u / \sum_i u_i$ with

$$u_i = \frac{2^{\,i-1}}{i!} \, P_{i-1}(\alpha), \qquad i = 1, \dots, N,$$

where $P_0(x) = 1$, $P_1(x) = x + 1$,

$$P_n(x) = (x + n) P_{n-1}(x) - \frac{n(n-1)}{4} P_{n-2}(x) \qquad (n \ge 2),$$

$P_N$ is the characteristic polynomial $\det(xI - J)$, and $\alpha$ is its largest root (the largest eigenvalue of $J$). The largest eigenvalue of $M$ is $1 + p\alpha$, so in the limit the number of viable cells grows by the factor $2(1 + p\alpha)$ per generation for one chromosome type, and by $2(1 + p\alpha)^{23}$ when the $23$ chromosome types missegregate independently and a cell dies if any of them leaves $[1, N]$.

For $N = 8$, $P_8(x) = x^8 + 36x^7 + 504x^6 + 3528x^5 + 13230x^4 + 26460x^3 + 26460x^2 + 11340x + \tfrac{2835}{2}$, and the limiting distribution has mode $1$ and mean close to $3$. The mixing time does depend on $p$: convergence is slower when $p$ is small.

## Expansion

The chain is irreducible and aperiodic on the viable states ($1 - ip > 0$), with one absorbing state, so by the Perron–Frobenius theory of absorbing chains its quasi-stationary distribution is the unique positive left eigenvector of $M$ for its largest eigenvalue, normalized to sum to one. Left eigenvectors of $M = I + pJ$ and $J$ coincide (eigenvalue $\lambda$ of $J$ becomes $1 + p\lambda$), which removes $p$. For a tridiagonal matrix with nonzero subdiagonal, expanding $\det(xI - J)$ along the last row gives the three-term recurrence, and solving $vJ = \lambda v$ row by row gives $v_i \propto P_{i-1}(\lambda) / \prod_{j=2}^{i} J_{j, j-1}$, with $\prod_{j=2}^{i} (j/2) = i!/2^{i-1}$. The source prints the recurrence with $+\frac{n(n-1)}{4}$; the sign must be negative because $J_{n,n-1} J_{n-1,n} > 0$, and the negative sign reproduces the source's printed $P_8$. In the extended model with chromosome scores the matrix becomes $DM$ with $D$ diagonal survival factors, and $p$-independence is lost.

## Sources

- S. Elizalde, A. M. Laughney and S. F. Bakhoum, "A Markov chain for numerical chromosomal instability in clonally expanding populations", PLoS Computational Biology 14 (2018), e1006447, Lemma 1, Theorem 2, Lemma 3, Eq. (3) and Theorem 4. <https://doi.org/10.1371/journal.pcbi.1006447> PMCID: PMC6150543.
