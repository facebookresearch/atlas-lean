# Coordinated epistasis

**Model.** For individuals $i = 1,\dots,n$ with genotypes $G_{ij}$ at markers $j = 1,\dots,M$, the polygenic pairwise epistasis model is

$$y_i = \sum_{j=1}^{M} G_{ij}\beta_j + \sum_{j \le j'} G_{ij}G_{ij'}\,\Omega_{jj'} + \varepsilon_i,$$

with marginal effects $\beta$, a symmetric matrix $\Omega$ of pairwise interaction effects, and independent identically distributed Gaussian errors $\varepsilon_i$. The additive model is $\Omega = 0$.

**Definition.** The *coordinated epistasis* of the architecture $(\beta, \Omega)$ is the covariance, across pairs of distinct markers, between the product of main effects and the interaction effect:

$$\gamma = \operatorname{Cov}_{j < j'}\bigl(\beta_j\beta_{j'},\; \Omega_{jj'}\bigr).$$

Diagonal terms $\Omega_{jj}$ (dominance of single variants) are excluded.

**Interpretation.** $\gamma > 0$ means interactions tend to amplify pairs of effects with the same sign (synergy), positively skewing the trait distribution and raising the chance of extreme high values; $\gamma < 0$ means antagonism between same-sign effects, dampening aggregate genetic effects relative to additivity. $\gamma = 0$ does not mean there is no epistasis, only that interaction effects are not aligned with main effects, as in isotropic models where $\Omega$ is drawn independently of $\beta$. The source proves that several architectures produce $\gamma \ne 0$: interacting latent pathways whose outputs combine nonlinearly, trans-regulatory models, polygenic molecular buffering, and gene–environment interaction with a heritable environment; and that latent interacting pathways exist if and only if $\gamma \ne 0$.

## Depends on

- [Genotypic value without epistasis](../../../../quantitative-genetics/fisher-s-decomposition-of-genetic-variance/total-value.md): the additive model $\Omega = 0$

## Expansion

Consider two pathways $P_1 = \sum_{j \in S_1} G_j\beta_j$ and $P_2 = \sum_{j \in S_2} G_j\beta_j$ and a trait $y = P_1 + P_2 + \delta P_1P_2 + \varepsilon$. Expanding the product gives $\Omega_{jj'} = \delta\,\beta_j\beta_{j'}$ for $j \in S_1$, $j' \in S_2$ and $0$ otherwise, so the interaction effects are exactly proportional to products of main effects on the cross-pathway pairs and $\gamma$ has the sign of $\delta$. Independent draws of $\Omega$ and $\beta$, by contrast, give $\gamma = 0$ in expectation whatever the size of $\Omega$, which is why heritability-based measures of the total size of $\Omega$ and the coordination $\gamma$ answer different questions.

## Sources

- B. Sheppard, N. Rappoport, P.-R. Loh, S. J. Sanders, N. Zaitlen and A. Dahl, "A model and test for coordinated polygenic epistasis in complex traits", Proceedings of the National Academy of Sciences of the USA (2021), "A model for coordinated epistasis", Eqs. 1–2, and SI Appendix, sections 3–4, <https://doi.org/10.1073/pnas.1922305118>, PMCID PMC8053945.
