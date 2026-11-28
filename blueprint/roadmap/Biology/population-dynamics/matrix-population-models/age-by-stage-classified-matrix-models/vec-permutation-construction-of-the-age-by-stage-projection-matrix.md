# Vec-permutation construction of the age-by-stage projection matrix

Consider a population with $s$ stages and $\omega$ age classes, recorded as an $s \times \omega$ matrix $N = (n_{ij})$ (rows stages, columns ages), with population vector $\tilde n = \operatorname{vec} N \in \mathbb{R}^{s\omega}$ (stages grouped within ages). The **vec-permutation matrix** $K = K_{s,\omega}$ is the $s\omega \times s\omega$ permutation matrix with $\operatorname{vec}(N^{\top}) = K \operatorname{vec} N$ for every $s\times\omega$ matrix $N$; explicitly $K_{s,\omega} = \sum_{i=1}^{s}\sum_{j=1}^{\omega} E_{ij} \otimes E_{ij}^{\top}$, where $E_{ij}$ is the $s\times\omega$ matrix unit.

The demographic input consists of: for each age $j$, an $s\times s$ matrix $U_j \ge 0$ of stage transitions and survival and an $s \times s$ fertility matrix $F_j \ge 0$; for each stage $i$, an $\omega\times\omega$ age-advancement matrix $D_i$ and an $\omega \times \omega$ matrix $H_i$ assigning offspring to age classes. Form the block-diagonal matrices

$$\mathbb{U} = \sum_{j=1}^{\omega} E_{jj} \otimes U_j, \quad \mathbb{F} = \sum_{j=1}^{\omega} E_{jj}\otimes F_j, \quad \mathbb{D} = \sum_{i=1}^{s} E_{ii}\otimes D_i, \quad \mathbb{H} = \sum_{i=1}^{s} E_{ii}\otimes H_i .$$

**Definition.** The age-by-stage projection matrices are

$$\tilde U = K^{\top}\mathbb{D}\,K\,\mathbb{U}, \qquad \tilde F = K^{\top}\mathbb{H}\,K\,\mathbb{F}, \qquad \tilde A = \tilde U + \tilde F,$$

and the population evolves as $\tilde n(t+1) = \tilde A\, \tilde n(t)$.

**Proposition (block-Leslie form).** If every $D_i$ has ones on the subdiagonal and in the $(\omega,\omega)$ corner and zeros elsewhere, and every $H_i$ has ones in its first row and zeros elsewhere, then $\tilde A$ is the block-Leslie matrix with $F_1, \dots, F_\omega$ in the first block row, $U_1, \dots, U_{\omega-1}$ on the block subdiagonal, and $U_\omega$ in the $(\omega,\omega)$ block; for $\omega = 3$,

$$\tilde A = \begin{pmatrix} F_1 & F_2 & F_3 \\ U_1 & 0 & 0 \\ 0 & U_2 & U_3\end{pmatrix}.$$

For any stage aggregation $R$ and age aggregation $C$, the identity $\operatorname{vec}(R N C) = (C^{\top} \otimes R)\operatorname{vec} N$ gives the marginal age distribution $(I_\omega \otimes \mathbf 1_s^{\top})\tilde n$ and the marginal stage distribution $(\mathbf 1_\omega^{\top} \otimes I_s)\tilde n$.

## Depends on

- [Leslie matrix](../../leslie-matrix-model/leslie-matrix.md)

## Expansion

Reading $\tilde U$ from right to left: $\mathbb{U}$ applies the age-specific stage transitions within each age class; $K$ regroups the vector so that ages are listed within stages; $\mathbb{D}$ advances each stage's age distribution; $K^{\top}$ restores the original grouping. Fertility is handled in the same way, with $\mathbb{H}$ sending newborns of every parental age to age class $1$. Multiplying out with the stated $D_i$ and $H_i$ moves the survivors of age class $j$ (after stage transitions by $U_j$) into age class $j+1$, keeps the last class open-ended, and collects all offspring in age class $1$, which is the block-Leslie pattern; with $s = 1$ it reduces to the ordinary Leslie matrix. Impossible age–stage combinations are encoded by zero rows and columns of $U_j$ and $F_j$, which makes $\tilde A$ reducible, but the dominant eigenvalue and eigenvectors of the irreducible part still give the growth rate, stable joint age–stage structure and reproductive values. The same block structure makes sensitivity analysis a chain rule through $\operatorname{vec}\tilde A$, $\operatorname{vec}\mathbb{U}$ and the $U_j$, e.g. $d\lambda / d\operatorname{vec}^{\top}\tilde A = w^{\top}\otimes v^{\top}$ for normalized right and left eigenvectors $w, v$.

## Sources

- H. Caswell, C. de Vries, N. Hartemink, G. Roth, S. F. van Daalen, "Age × stage-classified demographic analysis: a comprehensive approach", Ecological Monographs 88(4) (2018) 560–584, Eqs. (1)–(4), (10)–(14), and Box 2, <https://doi.org/10.1002/ecm.1306>, PMCID PMC6283253.
