# Sparse selection index for breeding-value prediction

**Setting.** Training phenotypes $y = (y_1, \dots, y_n)^\top$ (centred and corrected for non-genetic effects) follow $y = u + \varepsilon$
with independent $u \sim (0, \sigma_u^2 G)$ and $\varepsilon \sim (0, \sigma_\varepsilon^2 I)$, where $G$ is a pedigree or genomic relationship
matrix. For a selection candidate $i$ with breeding value $u_i$, let $G_i \in \mathbb{R}^n$ be its relationships to the training individuals,
so that $\operatorname{Cov}(y, u_i) = \sigma_u^2 G_i$, and let $\lambda_0 = \sigma_\varepsilon^2/\sigma_u^2 = (1 - h^2)/h^2$.

**Standard selection index.** The index $T_i = \beta_i^\top y$ minimizing $\tfrac12 E(u_i - \beta_i^\top y)^2$ solves

$$\hat\beta_i = \arg\min_{\beta_i} \Bigl\{ \tfrac12 \beta_i^\top (G + \lambda_0 I) \beta_i - G_i^\top \beta_i \Bigr\} = (G + \lambda_0 I)^{-1} G_i ,$$

and $\hat T_i = \hat\beta_i^\top y$ equals the BLUP of $u_i$ (pedigree BLUP or G-BLUP, according to $G$). When $G$ is a genomic relationship
matrix, $\hat\beta_i$ typically has no zero entries, so every training record contributes to every prediction.

**Sparse selection index (SSI).** For $\lambda \ge 0$,

$$\tilde\beta_i(\lambda) = \arg\min_{\beta_i} \Bigl\{ \tfrac12 \beta_i^\top (G + \lambda_0 I) \beta_i - G_i^\top \beta_i + \lambda \sum_{j=1}^n |\beta_{ij}| \Bigr\},$$

a strictly convex problem (since $G + \lambda_0 I \succ 0$) with a unique solution; $\tilde\beta_i(0) = \hat\beta_i$, and as $\lambda$ grows the
solution becomes sparse, selecting for each candidate its own subset of training individuals (support points). $\lambda$ is tuned to
maximize the prediction accuracy of $\tilde T_i = \tilde\beta_i^\top y$.

## Depends on

- [Hazel's selection index](hazel-selection-index.md)
- [Conditional expectation in the mixed model](../linear-mixed-models-and-blup/cond-exp-mixed-model.md)

## Expansion

Expanding $E(u_i - \beta_i^\top y)^2 = \sigma_u^2 + \beta_i^\top P \beta_i - 2\sigma_u^2 G_i^\top\beta_i$ with $P = \sigma_u^2 G + \sigma_\varepsilon^2 I$ and
dividing by $\sigma_u^2$ gives the quadratic objective, whose stationarity condition $(G + \lambda_0 I)\beta_i = G_i$ is the selection-index
normal equation. The SSI objective has exactly the form of a LASSO problem with Gram matrix $G + \lambda_0 I$ in place of $X^\top X$ and
$G_i$ in place of $X^\top y$, so it is solved by coordinate descent with soft-thresholding:
$\beta_{ij} \leftarrow S_\lambda\bigl(G_{ij} - \sum_{k\ne j} (G + \lambda_0 I)_{jk}\beta_{ik}\bigr)/(G_{jj} + \lambda_0)$, where
$S_\lambda(z) = \operatorname{sign}(z)(|z| - \lambda)_+$. (Lopez-Cruz and de los Campos 2021, Equations 1–3.)

## Sources

- M. Lopez-Cruz and G. de los Campos, "Optimal breeding-value prediction using a sparse selection index", Genetics (2021), <https://doi.org/10.1093/genetics/iyab030> (PMC8128408).
