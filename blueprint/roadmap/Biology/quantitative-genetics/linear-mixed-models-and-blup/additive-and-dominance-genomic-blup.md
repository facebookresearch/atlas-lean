# Additive-and-dominance genomic BLUP (DGBLUP)

Let $g \in \mathbb R^n$ be the vector of genotype means of $n$ individuals, $Q$ an $n \times c$ matrix of fixed covariates containing the intercept column (for example ones and principal components), $X \in \{0,1,2\}^{n\times m}$ the noncentered matrix of minor-allele counts at $m$ markers and $Z \in \{0,1\}^{n \times m}$ the noncentered matrix of heterozygosity indicators ($Z_{ij} = 1$ exactly when $X_{ij} = 1$). The dominance GBLUP model is

$$g = Q\delta + u + w + \varepsilon,\qquad u \sim N(0, G\sigma_u^2),\quad w \sim N(0, D\sigma_w^2),\quad \varepsilon \sim N(0, I\sigma_\varepsilon^2),$$

$$G = XX^\top/m, \qquad D = ZZ^\top/m,$$

with $u$, $w$, $\varepsilon$ independent; it is the marker model $g = Q\delta + X\beta + Z\gamma + \varepsilon$ with i.i.d. $\beta_j \sim N(0, \sigma_u^2/m)$ and $\gamma_j \sim N(0, \sigma_w^2/m)$. Setting $\sigma_w^2 = 0$ gives GBLUP. With $H = Q(Q^\top Q)^{-1}Q^\top$ and the covariate-adjusted kernels $\tilde G = (I - H)G(I - H)$, $\tilde D = (I - H)D(I - H)$, the proportions of variance explained by additive and dominance marker effects are

$$\frac1n\sum_{i=1}^n \frac{\tilde G_{ii}\sigma_u^2}{\tilde G_{ii}\sigma_u^2 + \tilde D_{ii}\sigma_w^2 + \sigma_\varepsilon^2}, \qquad \frac1n\sum_{i=1}^n \frac{\tilde D_{ii}\sigma_w^2}{\tilde G_{ii}\sigma_u^2 + \tilde D_{ii}\sigma_w^2 + \sigma_\varepsilon^2}.$$

Partitioning markers into annotation bins $k$ (additive) and $l$ (dominance) replaces $G\sigma_u^2$ by $\sum_k G_k\sigma_k^2$ with $G_k = X_kX_k^\top/m_k$, and $D\sigma_w^2$ by $\sum_l D_l\sigma_l^2$ with $D_l = Z_lZ_l^\top/m_l$.

**Proposition (confounding with two genotype classes).** If at every marker only two genotype classes occur in the sample (as in hybrids that all share one inbred parent, which are either homozygous for the tester allele or heterozygous), then each column satisfies $z_j = a_j x_j + c_j\mathbf 1$ for constants $a_j, c_j$, so $Z = XA + \mathbf 1 c^\top$ with $A$ diagonal. Hence $Z\gamma = X(A\gamma) + \mathbf 1(c^\top\gamma)$: dominance marker effects are a reparametrization of additive effects plus an intercept, and additive and dominance effects are not separately identifiable from $g$.

## Depends on

- [BLUP is the conditional expectation](cond-exp-mixed-model.md)

## Expansion

The kernel form follows from $\operatorname{Var}(X\beta) = XX^\top\sigma_u^2/m$ and $\operatorname{Var}(Z\gamma) = ZZ^\top\sigma_w^2/m$, and the BLUPs of $u$ and $w$ are the conditional expectations $G\sigma_u^2 V^{-1}(g - Q\delta)$ and $D\sigma_w^2 V^{-1}(g - Q\delta)$ with $V = G\sigma_u^2 + D\sigma_w^2 + I\sigma_\varepsilon^2$. Projecting out the fixed effects removes the part of each kernel's diagonal explained by $Q$, which is why the adjusted diagonals enter the variance proportions. For the confounding statement, a column taking only two values $\{x_0, x_1\}$ has a heterozygosity indicator that is an affine function of it, since any function on a two-point set is affine; the same holds for an intercept absorbed by $Q$. Ramstein et al. (2020) fit the dominance model only in the panel with several testers for this reason, and report that adding dominance and functional enrichments improved prediction of agronomic traits in hybrid maize.

## Sources

- G. P. Ramstein, S. J. Larsson, J. P. Cook et al., "Dominance effects and functional enrichments improve prediction of agronomic traits in hybrid maize", Genetics 215(1) (2020), 215–230, <https://doi.org/10.1534/genetics.120.303025>, PMCID PMC7198274 (GBLUP, model (1), model (3) and the variance-partition formulas).
