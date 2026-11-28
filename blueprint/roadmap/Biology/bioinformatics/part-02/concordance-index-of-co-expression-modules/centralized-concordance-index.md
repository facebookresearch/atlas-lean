# Centralized concordance index

Let $G \in \mathbb{R}^{n \times N}$ ($n \ge 2$ genes, $N \ge 3$ samples) have rows $g_1, \dots, g_n$, the expression profiles of a candidate co-expression module, each row nonconstant. Let $\rho(g_i, g_j)$ denote the Pearson correlation of rows $i$ and $j$.

**Proposition 1 (rank of a perfectly co-expressed module).** If $|\rho(g_i, g_j)| = 1$ for all $i, j$, then $\operatorname{rank} G \le 2$; this is unchanged by shifting or scaling any row. Consequently, with singular values $S_{11} \ge S_{22} \ge \cdots$ of $G$, the ratio $R_{12} = (S_{11}^2 + S_{22}^2)/\|G\|_F^2$ equals $1$.

**Proposition 2 (centred and standardized profiles).** Let $\hat G$ be obtained by centring each row, $g_i^c = g_i - \bar g_i \mathbf{1}^{\mathsf T}$, and scaling it to unit Euclidean norm, $\hat g_i = g_i^c / \|g_i^c\|$. Then $\hat g_i \hat g_j^{\mathsf T} = \rho(g_i, g_j)$ for all $i, j$, $\|\hat G\|_F^2 = n$, and if $|\rho(g_i, g_j)| = 1$ for all pairs then $\operatorname{rank} \hat G = 1$, i.e. $\hat G = (\pm 1, \dots, \pm 1)^{\mathsf T} \hat g_1$.

**Definition.** With $\hat S_{11}$ the largest singular value of $\hat G$, the **centralized concordance index** is

$$\mathrm{CCI} = \frac{\hat S_{11}^2}{n}.$$

It satisfies $0 < \mathrm{CCI} \le 1$, with $\mathrm{CCI} = 1$ iff every pair of rows has $|\rho| = 1$. Equivalently, $n \cdot \mathrm{CCI}$ is the largest eigenvalue of the $n \times n$ correlation matrix $\hat G \hat G^{\mathsf T}$, so CCI is the fraction of total standardized variance captured by the leading principal component of the module. Its significance is assessed against row-permuted data or random gene sets of the same size.

## Expansion

If $|\rho(g_i, g_1)| = 1$ then $g_i = \alpha_i g_1 + \beta_i \mathbf{1}^{\mathsf T}$, so $G = a\, g_1 + b\, \mathbf{1}^{\mathsf T}$ for column vectors $a, b$, a sum of two rank-one matrices; subadditivity of rank gives Proposition 1, and $\|G\|_F^2 = \sum_k S_{kk}^2$ gives $R_{12} = 1$. Centring removes the $\mathbf{1}^{\mathsf T}$ component and scaling makes the inner products of rows equal to correlations, which gives Proposition 2. Since $\hat S_{11}^2$ is the top eigenvalue of the correlation matrix, whose trace is $n$, it lies in $[n/\operatorname{rank}\hat G, n]$; it equals $n$ iff the correlation matrix has rank one, which for unit diagonal forces all off-diagonal entries to be $\pm 1$. Unlike average-correlation module density, CCI is driven by the dominant common direction and is less sensitive to a few outlier genes or to an interfering second module.

## Sources

- Z. Han, J. Zhang, G. Sun, G. Liu and K. Huang, "A matrix rank based concordance index for evaluating and detecting conditional specific co-expressed gene modules", BMC Genomics (2016), Methods, Eqs. (1)–(11), Propositions 1–2, <https://doi.org/10.1186/s12864-016-2912-y>, PMCID PMC5001231.
