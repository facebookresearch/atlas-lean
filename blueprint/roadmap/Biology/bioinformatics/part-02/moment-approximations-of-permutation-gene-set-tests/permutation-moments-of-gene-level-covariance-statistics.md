# Permutation moments of gene-level covariance statistics

**Setting.** An experiment has $n$ subjects, expression values $X_{gi}$ for genes $g$ and a target variable $Y_i$ (treatment or phenotype), each centered: $\sum_i Y_i = \sum_i X_{gi} = 0$. The association of gene $g$ with $Y$ is $\hat\beta_g = \frac1n\sum_{i=1}^n X_{gi}Y_i$. Permuting $Y$ uniformly at random (with $X, Y$ fixed) gives $\tilde\beta_g$. Write

$$\mu_2 = \tfrac1n\textstyle\sum_i Y_i^2,\quad \mu_4 = \tfrac1n\sum_i Y_i^4,\quad \bar X_{gh} = \tfrac1n\sum_i X_{gi}X_{hi},\quad \bar X_{ghrs} = \tfrac1n\sum_i X_{gi}X_{hi}X_{ri}X_{si}.$$

**Second moments (Lemma 1, Corollary 1).** For $n\ge 2$, $\mathbb{E}\tilde\beta_g = 0$ and

$$\mathbb{E}[\tilde\beta_g\tilde\beta_h] = \operatorname{cov}(\tilde\beta_g,\tilde\beta_h) = \frac{\mu_2\,\bar X_{gh}}{n-1}.$$

So under permutation the correlation of $\tilde\beta_g$ and $\tilde\beta_h$ equals the sample correlation of genes $g$ and $h$.

**Fourth moments (Lemma 2).** For $n \ge 4$,

$$\mathbb{E}[\tilde\beta_g\tilde\beta_h\tilde\beta_r\tilde\beta_s] = \begin{pmatrix}\mu_2^2 & \mu_4\end{pmatrix} A^{\top}B \begin{pmatrix}\bar X^{*}_{ghrs}/n^2\\ \bar X_{ghrs}/n^3\end{pmatrix},\qquad \bar X^{*}_{ghrs} = \bar X_{gh}\bar X_{rs} + \bar X_{gr}\bar X_{hs} + \bar X_{gs}\bar X_{hr},$$

with the $5\times 2$ matrices (rows indexed by the index patterns four-of-a-kind, three-of-a-kind, two pairs, one pair, all distinct)

$$A = \begin{pmatrix} 0 & 1\\ 0 & -\frac{1}{n-1}\\ \frac{n}{n-1} & -\frac{1}{n-1}\\ -\frac{n}{(n-1)(n-2)} & \frac{2}{(n-1)(n-2)}\\ \frac{3n}{(n-1)(n-2)(n-3)} & -\frac{6}{(n-1)(n-2)(n-3)}\end{pmatrix},\qquad B = \begin{pmatrix}0&1\\0&-4\\1&-3\\-2&12\\1&-6\end{pmatrix}.$$

In particular $\operatorname{cov}(\tilde\beta_g^2,\tilde\beta_h^2)$ follows by taking $(g,g,h,h)$ and subtracting $\mathbb{E}\tilde\beta_g^2\,\mathbb{E}\tilde\beta_h^2$.

## Expansion

Under a uniform permutation $\mathbb{E}[\tilde Y_i\tilde Y_{i'}] = \mu_2$ if $i = i'$ and $-\mu_2/(n-1)$ otherwise, because $\sum_i Y_i = 0$; summing against $X_{gi}X_{hi'}$ and using $\sum_i X_{gi} = 0$ leaves $\frac{n}{n-1}\mu_2\sum_i X_{gi}X_{hi}$. For fourth moments, the five permutation moments $\mathbb{E}\tilde Y_i^4,\ \mathbb{E}\tilde Y_i^3\tilde Y_j,\ \mathbb{E}\tilde Y_i^2\tilde Y_j^2,\ \mathbb{E}\tilde Y_i^2\tilde Y_j\tilde Y_k,\ \mathbb{E}\tilde Y_i\tilde Y_j\tilde Y_k\tilde Y_\ell$ over distinct indices are linear in $(\mu_2^2,\mu_4)$ (matrix $A$), obtained by rewriting sums over distinct indices as unrestricted sums, most of which vanish by centering. The matching sums of products of $X$'s are linear in $(\bar X^{*}/n^2, \bar X/n^3)$ (matrix $B$). Only $O(1)$ moments of $Y$ and pairwise and fourfold cross-moments of $X$ are needed, and the formulas were checked against full enumeration on a small data set.

## Sources

- Larson JL, Owen AB. Moment based gene set tests. *BMC Bioinformatics* 16:132 (2015), Methods: Lemma 1, Corollary 1, Lemma 2, Corollary 2, Eq. 6. <https://doi.org/10.1186/s12859-015-0571-7>. PMCID: PMC4419444.
