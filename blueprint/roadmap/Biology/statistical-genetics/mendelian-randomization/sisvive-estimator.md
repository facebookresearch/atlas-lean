# The sisVIVE estimator

In the setting of [identification with some invalid instruments](identification-with-some-invalid-instruments.md), with data $Y \in \mathbb R^n$, $D \in \mathbb R^n$ and $Z \in \mathbb R^{n\times L}$ of full column rank, let $P_Z = Z(Z^\top Z)^{-1}Z^\top$ be the projection onto the column space of $Z$. The ideal estimator under the bound $s < U$ is the $\ell_0$-constrained problem

$$\min_{\alpha, \beta}\; \tfrac12\big\|P_Z(Y - Z\alpha - D\beta)\big\|_2^2 \quad \text{subject to } \|\alpha\|_0 < U,$$

which is combinatorial. The **some invalid, some valid instrumental variable estimator** (sisVIVE) replaces it by its convex $\ell_1$ relaxation in Lagrangian form: for a tuning parameter $\lambda > 0$,

$$(\hat\alpha_\lambda, \hat\beta_\lambda) \in \arg\min_{\alpha \in \mathbb R^L,\, \beta \in \mathbb R}\; \tfrac12\big\|P_Z(Y - Z\alpha - D\beta)\big\|_2^2 + \lambda\|\alpha\|_1 .$$

The estimated invalid instruments are $\operatorname{supp}(\hat\alpha_\lambda)$ and $\hat\beta_\lambda$ estimates the causal effect. If the valid set were known and $\alpha$ restricted to the invalid coordinates, the unpenalized minimizer would be the two-stage least-squares estimator using the valid instruments.

## Depends on

- [Identification of a causal effect when some instruments are invalid](identification-with-some-invalid-instruments.md)

## Expansion

Because $\beta$ is unpenalized, for fixed $\alpha$ the optimal $\beta$ is a least-squares coefficient of $P_Z(Y - Z\alpha)$ on $P_Z D$. Substituting it reduces the problem to a lasso in $\alpha$ with a design projected orthogonally to $P_Z D$, which the paper solves by a two-step algorithm (Theorem 3). Estimation error bounds hold under restricted isometry conditions on that projected design (Theorem 2); $\lambda$ is chosen by cross-validation in practice. Section 3.2, Equations (8)–(10).

## Sources

- H. Kang, A. Zhang, T. T. Cai, D. S. Small, "Instrumental Variables Estimation With Some Invalid Instruments and its Application to Mendelian Randomization", Journal of the American Statistical Association 111 (2016), 132–144, <https://doi.org/10.1080/01621459.2014.994705>.
