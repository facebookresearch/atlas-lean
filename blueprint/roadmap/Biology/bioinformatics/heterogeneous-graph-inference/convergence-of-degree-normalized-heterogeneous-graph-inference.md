# Convergence of degree-normalized heterogeneous graph inference

Let $S_R \in \mathbb{R}^{m \times m}$ (miRNA similarity) and $S_D \in \mathbb{R}^{n \times n}$ (disease similarity) be symmetric matrices with nonnegative entries and strictly positive row sums $d^R_i = \sum_l S_R(i, l)$ and $d^D_j = \sum_l S_D(j, l)$. Their degree-normalized versions are

$$\tilde S_R(i, j) = \frac{S_R(i, j)}{\sqrt{d^R_i \, d^R_j}}, \qquad \tilde S_D(i, j) = \frac{S_D(i, j)}{\sqrt{d^D_i \, d^D_j}},$$

that is, $\tilde S_R = D_R^{-1/2} S_R D_R^{-1/2}$ and $\tilde S_D = D_D^{-1/2} S_D D_D^{-1/2}$ with $D_R, D_D$ the diagonal degree matrices. Let $A^* \in \mathbb{R}^{m \times n}$ be a prior miRNA-disease association matrix and $0 < a < 1$ a decay factor. Heterogeneous graph inference iterates

$$P_{t+1} = a \, \tilde S_R \, P_t \, \tilde S_D + (1 - a) A^*, \qquad t = 0, 1, 2, \dots$$

**Claim.** For every starting matrix $P_0 \in \mathbb{R}^{m \times n}$, $P_t$ converges to

$$P^* = (1 - a) \sum_{k \ge 0} a^k \, \tilde S_R^{\,k} A^* \tilde S_D^{\,k},$$

the unique solution of $P = a \tilde S_R P \tilde S_D + (1 - a) A^*$; equivalently $\operatorname{vec}(P^*) = (1 - a)\,(I - a\, \tilde S_D \otimes \tilde S_R)^{-1} \operatorname{vec}(A^*)$. Moreover $\|P_t - P^*\|_F \le a^t \|P_0 - P^*\|_F$.

The entry $P^*(m_0, d_0)$ is a decaying sum over paths miRNA $\to$ (similar miRNAs)$^k$ $\to$ known association $\to$ (similar diseases)$^k$ $\to$ disease; the $k = 1$ term is the length-three path score $\sum_{i, j} \tilde S_R(m_i, m_0)\, A^*(m_i, d_j)\, \tilde S_D(d_j, d_0)$.

## Expansion

$\tilde S_R = D_R^{1/2} (D_R^{-1} S_R) D_R^{-1/2}$ is similar to the row-stochastic matrix $D_R^{-1} S_R$, whose spectral radius is $1$. Since $\tilde S_R$ is symmetric, its spectral norm equals its spectral radius, so $\|\tilde S_R\|_2 \le 1$, and likewise $\|\tilde S_D\|_2 \le 1$. Hence the linear map $L(P) = \tilde S_R P \tilde S_D$ satisfies $\|L(P)\|_F \le \|\tilde S_R\|_2 \|P\|_F \|\tilde S_D\|_2 \le \|P\|_F$, and the affine update $P \mapsto a L(P) + (1 - a) A^*$ is a contraction with factor $a$ in the Frobenius norm. The Banach fixed-point theorem gives existence, uniqueness and the geometric rate; unrolling the recursion gives the Neumann series. Without the symmetric normalization (for example with raw similarities satisfying $a\,\rho(S_R)\,\rho(S_D) > 1$, where $\rho$ is the spectral radius) the iteration can diverge.

## Sources

- X. Chen, J. Yin, J. Qu and L. Huang, "MDHGI: Matrix decomposition and heterogeneous graph inference for miRNA-disease association prediction", PLoS Computational Biology 14 (2018), e1006418, Eqs. (22)–(25) (the convergence statement is the paper's Theorem 1, proved in its supplementary text). <https://doi.org/10.1371/journal.pcbi.1006418> PMCID: PMC6126877.
