# Exact multivariate mixed-model association by eigen-rotation and simultaneous diagonalization

Let $Y \in \mathbb{R}^{n \times d}$ hold $d$ phenotypes of $n$ individuals, $W \in \mathbb{R}^{n \times c}$ covariates, $x \in \mathbb{R}^n$ the genotypes of the tested SNP and $K$ a known symmetric positive semidefinite relatedness matrix. The multivariate linear mixed model (mvLMM) with one variance component is

$$Y = WA + x\beta^\top + G + E, \qquad \operatorname{vec}(G) \sim N(0, V_g \otimes K), \qquad \operatorname{vec}(E) \sim N(0, V_e \otimes I_n),$$

with $A \in \mathbb{R}^{c\times d}$, $\beta \in \mathbb{R}^d$, $V_g$ positive semidefinite and $V_e$ positive definite $d \times d$ matrices. Write $K = U \operatorname{diag}(\lambda_1,\dots,\lambda_n) U^\top$ with $U$ orthogonal.

**Proposition.**

1. *(Row decoupling.)* The rotated rows $\tilde y_i^\top$ of $U^\top Y$ are independent with $\tilde y_i \sim N\big(A^\top \tilde w_i + \beta\tilde x_i,\ \lambda_i V_g + V_e\big)$, where $\tilde w_i^\top$ and $\tilde x_i$ are the rows of $U^\top W$ and $U^\top x$.
2. *(Trait decoupling.)* Let $V_e^{-1/2} V_g V_e^{-1/2} = Q \operatorname{diag}(\delta_1,\dots,\delta_d) Q^\top$ with $Q$ orthogonal and put $S = Q^\top V_e^{-1/2}$. Then $S(\lambda_i V_g + V_e)S^\top = \operatorname{diag}(\lambda_i\delta_k + 1)_{k=1}^d$, so after transforming each $\tilde y_i$ by $S$ the $nd$ scalar responses are independent with variances $\lambda_i\delta_k + 1$.
3. *(Cost.)* Hence the log-likelihood, with determinant $\sum_i \log\det(\lambda_i V_g + V_e)$, and its derivatives in $(V_g, V_e)$ can be evaluated without any $nd \times nd$ inverse. After one $O(n^3)$ eigendecomposition shared by all SNPs, each SNP costs $O(n^2)$ to rotate $x$ plus optimization iterations linear in $n$, which makes the exact likelihood-ratio test of $H_0 : \beta = 0$, with $V_g$ and $V_e$ re-estimated under both hypotheses for every SNP, feasible genome-wide.

## Expansion

1. $\operatorname{vec}(U^\top G) = (I_d \otimes U^\top)\operatorname{vec}(G)$ has covariance $V_g \otimes \operatorname{diag}(\lambda_i)$, and $U^\top E$ keeps covariance $V_e \otimes I_n$; reading the Kronecker structure row by row gives independent rows with covariance $\lambda_i V_g + V_e$.
2. $S V_e S^\top = Q^\top Q = I_d$ and $S V_g S^\top = \operatorname{diag}(\delta_k)$, so a single $d \times d$ transformation simultaneously diagonalizes every row covariance.
3. In these coordinates the generalized least-squares estimates of $(A, \beta)$ for fixed $(V_g, V_e)$ are weighted sums over $nd$ independent observations, and the expectation-maximization and Newton–Raphson updates for $(V_g, V_e)$ use only these sums. Compared with re-fitting by generic REML software, the per-SNP $O(n^3)$ cost disappears; the paper reports $O(n^3 + n^2 d + n^2 c + s(n^2 + t_1 n c^2 d^2 + t_2 n c^2 d^6))$ for $s$ SNPs with $t_1$ EM and $t_2$ NR iterations. The univariate case $d = 1$ recovers the rotation of the linked article.

## Sources

- X. Zhou and M. Stephens, "Efficient multivariate linear mixed model algorithms for genome-wide association studies", Nature Methods 11 (2014), 407–409, Table 1 and Supplementary Note, <https://doi.org/10.1038/nmeth.2848> (PMC4211878).
