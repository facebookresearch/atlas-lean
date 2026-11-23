# Cross-trait scaled-score identity with equal in-sample LD

Let a [bivariate LD-score model](cross-trait-model.md) on a measure $\mu$ have samples $S_1, S_2$ of sizes $N_1, N_2$, let $X$ be a real $n \times M$ genotype matrix, and let $j$ be a marker such that $r^{S_1}_{jk} = r^{S_2}_{jk}$ for every marker $k$ and $\sum_{i \in S_1 \cap S_2} X_{ij}^2 = N_s$, where $N_s = |S_1 \cap S_2|$. Then

$$\int z^{(1)}_j z^{(2)}_j \, d\mu = \frac{\sqrt{N_1 N_2}\, \rho_g\, \ell_j}{M} + \frac{\rho_e N_s}{\sqrt{N_1 N_2}}, \qquad \ell_j = \sum_{k=1}^{M} \bigl(r^{S_1}_{jk}\bigr)^2,$$

where $z^{(1)}, z^{(2)}$ are the [scaled marginal scores](z1.md) and $r^{S}$ the [in-sample normalized cross products](sample-corr.md), with the convention $x/0 = 0$. Here $\rho_e$ is only the residual cross-moment of the model, not a phenotypic correlation.
