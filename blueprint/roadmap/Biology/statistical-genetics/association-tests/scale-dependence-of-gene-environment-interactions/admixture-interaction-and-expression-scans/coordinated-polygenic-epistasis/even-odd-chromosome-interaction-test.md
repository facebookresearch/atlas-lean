# Even–odd chromosome interaction test

In the [coordinated epistasis model](coordinated-epistasis.md), split the genome into two sets of chromosomes without linkage disequilibrium between them, for concreteness the odd-numbered and the even-numbered chromosomes, and build polygenic risk scores $\mathrm{PRS}_o$ and $\mathrm{PRS}_e$ from the markers of each set (with effect estimates from an independent sample). Fit by ordinary least squares

$$y \sim \alpha_o\,\mathrm{PRS}_o + \alpha_e\,\mathrm{PRS}_e + \gamma_{eo}\,\mathrm{PRS}_o\cdot\mathrm{PRS}_e .$$

**Properties (stated in the source under the model and with many causal markers).**

- $\gamma_{eo} = 0$ if and only if $\gamma = 0$, so a regression test of $\hat\gamma_{eo}$ tests for coordinated epistasis.
- When causal markers are in linkage equilibrium, $\hat\gamma_{eo}$ is unbiased and consistent for its target, and under an infinitesimal epistatic model the downward bias in $|\gamma|$ caused by interacting pairs that fall on the same side of the split can be corrected, because a random split separates exactly half of all interacting pairs in expectation.
- Under a perfectly infinitesimal model every split of the chromosomes into two groups gives the same result.

Splitting by whole chromosomes keeps the two scores free of shared variants and linkage, so nonlinear effects of single variants (dominance) cannot masquerade as interaction between the scores. In finite genomes the estimate depends on the split, and in practice interactions between all pairs of chromosome-specific scores are tested jointly with an $F$-test.

## Depends on

- [Coordinated epistasis](coordinated-epistasis.md)
- [Ordinary least-squares estimator](../../../../../../Probability/linear-models-multivariate/ordinary-least-squares/sampling-properties-of-the-ordinary-least-square/ols-estimator.md): the fit of the interaction regression

## Expansion

The randomly defined halves act as proxies for the unknown interacting pathways. Writing each score as a sum over its markers, the product $\mathrm{PRS}_o\,\mathrm{PRS}_e$ is a sum of terms $G_jG_{j'}\beta_j\beta_{j'}$ over cross pairs $j \in o$, $j' \in e$, and its regression coefficient on $y$ picks up the interaction effects $\Omega_{jj'}$ of exactly those pairs, weighted by $\beta_j\beta_{j'}$. Pairs that the split assigns to the same side contribute nothing and cause no bias, only power loss; pairs that it separates contribute in proportion to the coordination. Since each interacting pair is separated with probability $1/2$, a nonzero $\gamma$ leaves a nonzero signal whatever the split.

## Sources

- B. Sheppard, N. Rappoport, P.-R. Loh, S. J. Sanders, N. Zaitlen and A. Dahl, "A model and test for coordinated polygenic epistasis in complex traits", Proceedings of the National Academy of Sciences of the USA (2021), "The EO test" (Eq. 3) and SI Appendix, section 3 and Proposition 1, <https://doi.org/10.1073/pnas.1922305118>, PMCID PMC8053945.
