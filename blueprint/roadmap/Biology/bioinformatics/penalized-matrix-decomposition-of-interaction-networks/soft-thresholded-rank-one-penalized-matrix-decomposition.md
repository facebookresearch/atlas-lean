# Soft-thresholded rank-one penalized matrix decomposition

**Problem.** Let $X\in\mathbb{R}^{n\times p}$ be a data matrix, for example the normalised adjacency matrix of a protein–protein interaction network. The rank-one penalized matrix decomposition with $L_1$ penalties, $\mathrm{PMD}(L_1, L_1)$, is

$$\max_{u\in\mathbb{R}^n,\,v\in\mathbb{R}^p} u^{\mathsf T}Xv\quad\text{s.t.}\quad \lVert u\rVert_2^2\le 1,\ \lVert v\rVert_2^2\le 1,\ \lVert u\rVert_1\le c_1,\ \lVert v\rVert_1\le c_2,$$

with $1\le c_1\le\sqrt n$ and $1\le c_2\le\sqrt p$ (smaller $c$ gives sparser factors), and $\delta = u^{\mathsf T}Xv$. Without the $L_1$ constraints its solution is the leading singular triple of $X$. Higher factors are obtained by deflation, $X_{r+1} = X_r - \delta_ru_rv_r^{\mathsf T}$, using

$$\tfrac12\big\lVert X - U\Delta V^{\mathsf T}\big\rVert_F^2 = \tfrac12\lVert X\rVert_F^2 - \sum_{r=1}^R\delta_r\,u_r^{\mathsf T}Xv_r + \tfrac12\sum_{r=1}^R\delta_r^2$$

for orthonormal columns $u_r, v_r$ and diagonal $\Delta = \operatorname{diag}(\delta_r)$.

**Theorem (soft-thresholding solution).** Let $S(a, c) = \operatorname{sgn}(a)(|a| - c)_+$ act componentwise. For $a\in\mathbb{R}^n$, $a \neq 0$, and $c\ge 1$, the problem

$$\max_u u^{\mathsf T}a\quad\text{s.t.}\quad\lVert u\rVert_2^2\le 1,\ \lVert u\rVert_1\le c$$

is solved by

$$u = \frac{S(a, \Delta)}{\lVert S(a, \Delta)\rVert_2},$$

where $\Delta = 0$ if this yields $\lVert u\rVert_1\le c$, and otherwise $\Delta > 0$ is chosen so that $\lVert u\rVert_1 = c$ (found by binary search).

**Algorithm.** The problem is biconvex: for fixed $v$ it is the theorem with $a = Xv$, for fixed $u$ with $a = X^{\mathsf T}u$. Alternate $u\leftarrow S(Xv,\Delta_1)/\lVert S(Xv,\Delta_1)\rVert_2$ and $v\leftarrow S(X^{\mathsf T}u,\Delta_2)/\lVert S(X^{\mathsf T}u,\Delta_2)\rVert_2$ until convergence, then set $\delta = u^{\mathsf T}Xv$. Each step does not decrease the objective. In protein-complex detection, the proteins with non-zero entries in a sparse factor form a candidate complex; predictions $p$ are matched to reference complexes $g$ by the overlap score $\mathrm{os}(p,g) = |C_p\cap C_g|^2/(|C_p|\,|C_g|)$ with a threshold such as $0.2$.

## Expansion

The theorem is the KKT solution of a linear objective over the intersection of the Euclidean ball and the $L_1$ ball. The Lagrangian $u^{\mathsf T}a - \tfrac{\mu}{2}\lVert u\rVert_2^2 - \Delta\lVert u\rVert_1$ is maximised componentwise by $u_i\propto S(a_i,\Delta)$; normalising enforces the $L_2$ constraint, and complementary slackness says $\Delta = 0$ unless the $L_1$ constraint binds. Soft-thresholding zeroes the coordinates with small $|a_i|$, which is what makes the factors sparse and interpretable as protein modules in a sparse network.

## Sources

- B. Cao, S. Deng, H. Qin, P. Ding, S. Chen, G. Li, *Detection of protein complexes based on penalized matrix decomposition in a sparse protein–protein interaction network*, Molecules 23 (2018), 1460, Section 3.2 (Eqs. 1–8, Theorem 1, Algorithms 1–3). <https://doi.org/10.3390/molecules23061460> (PMCID: PMC6100434)
- D. M. Witten, R. Tibshirani, T. Hastie, *A penalized matrix decomposition, with applications to sparse principal components and canonical correlation analysis*, Biostatistics 10 (2009), 515–534. <https://doi.org/10.1093/biostatistics/kxp008>
