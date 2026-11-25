# Certified evaluation of the expected site frequency spectrum for piecewise-constant population size

This page covers a research target. For a population whose size is piecewise constant, with finitely many epochs of positive sizes and rational breakpoints, the expected epoch lengths $\mathbb{E}[T_k]$ of the coalescent have closed forms as finite sums of exponentials, and the [expected site frequency spectrum](integral-sfs-of-indep.md) $\mathbb{E}[\xi_i]$ is $\theta$ times a fixed linear image of $(\mathbb{E}[T_k])_k$. The target is an interval-arithmetic algorithm, with outward rounding as the model of enclosure, that returns enclosures of every $\mathbb{E}[\xi_i]$ with rigorous error bounds, despite the cancellation between terms of alternating sign in the closed form.

## Expansion

Split the target into separately stated results, each with hypotheses fixed from a source:

1. The closed form of $\mathbb{E}[T_k]$ as a finite sum of exponentials for piecewise-constant size.
2. Correctness of the enclosures under outward rounding.
3. A check against the constant-size neutral case, where $\mathbb{E}[\xi_i] = \theta / i$.

Prerequisites:

- [Expected SFS under a variable population size](integral-sfs-of-indep.md)

## Sources

- R. N. Gutenkunst, R. D. Hernandez, S. H. Williamson and C. D. Bustamante, Inferring the joint demographic history of multiple populations from multidimensional SNP frequency data, *PLoS Genet.* 5 (2009), e1000695, <https://doi.org/10.1371/journal.pgen.1000695> (the spectrum computed numerically on grids).
