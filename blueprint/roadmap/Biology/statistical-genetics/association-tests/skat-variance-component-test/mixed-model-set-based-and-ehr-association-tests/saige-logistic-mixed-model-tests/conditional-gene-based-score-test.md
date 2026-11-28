# Conditional gene-based score test

In the null generalized linear mixed model of the [region-based statistics](glmm-burden-skat-and-skat-o-statistics.md), let $\tilde G$ ($N \times q$) be the covariate-adjusted genotypes of a tested region and $\tilde G_2$ ($N \times q_2$) those of conditioning markers, with scores $S = \tilde G^\top (Y - \hat\mu)$ and $S_2 = \tilde G_2^\top (Y - \hat\mu)$. Under the null hypothesis that the tested region has no effect, $(S, S_2)$ is approximately multivariate normal with covariance

$$\begin{pmatrix} \tilde G^\top \hat P \tilde G & \tilde G^\top \hat P \tilde G_2 \\ \tilde G_2^\top \hat P \tilde G & \tilde G_2^\top \hat P \tilde G_2 \end{pmatrix},$$

and hence

$$\mathbb{E}(S \mid S_2) = \tilde G^\top \hat P \tilde G_2 \bigl(\tilde G_2^\top \hat P \tilde G_2\bigr)^{-1} S_2,$$

$$\operatorname{Var}(S \mid S_2) = \tilde G^\top \hat P \tilde G - \tilde G^\top \hat P \tilde G_2 \bigl(\tilde G_2^\top \hat P \tilde G_2\bigr)^{-1} \tilde G_2^\top \hat P \tilde G.$$

Burden, SKAT and SKAT-O $p$-values conditional on the markers are computed from this conditional normal law, using only the unconditional scores and the linkage disequilibrium between tested and conditioning markers.

## Depends on

- [Burden, SKAT and SKAT-O statistics under a generalized linear mixed model](glmm-burden-skat-and-skat-o-statistics.md)

## Expansion

This is the Gaussian conditioning formula applied to the joint score vector; the conditioning markers' own effects shift the mean of $S_2$ and, through the cross-covariance, the mean of $S$, which the conditional mean removes.

## Sources

- W. Zhou et al., *Scalable generalized linear mixed model for region-based association tests in large biobanks and cohorts*, Nat. Genet. 52 (2020), 634–639. <https://doi.org/10.1038/s41588-020-0621-6> (PMCID: PMC7871731) Online Methods, "Conditional analysis".
