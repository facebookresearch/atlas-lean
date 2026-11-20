# Cross-trait scaled-score identity, exact form

For every [bivariate LD-score model](cross-trait-model.md) on a measure $\mu$ with samples $S_1, S_2$ of sizes $N_1 = |S_1|$, $N_2 = |S_2|$, every real $n \times M$ genotype matrix $X$ and every marker $j$,

$$\int z^{(1)}_j z^{(2)}_j \, d\mu = \sqrt{N_1 N_2}\, \frac{\rho_g}{M} \sum_{k=1}^{M} r^{S_1}_{jk} r^{S_2}_{jk} + \frac{\rho_e}{\sqrt{N_1 N_2}} \sum_{i \in S_1 \cap S_2} X_{ij}^2,$$

where $z^{(1)}, z^{(2)}$ are the [scaled marginal scores](z1.md) and $r^{S}$ the [in-sample normalized cross products](sample-corr.md), with the convention $x/0 = 0$.
