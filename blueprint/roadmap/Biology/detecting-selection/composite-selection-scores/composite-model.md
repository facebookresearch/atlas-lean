# Composite selection score model

Let $k$ be a natural number and $\Sigma_1, \dots, \Sigma_k$ sets (the value spaces of $k$ component statistics). A composite-score model consists of a real number $\pi$ with $0 < \pi < 1$ (the prior probability that the site is under selection) and, for each component $i$, functions $s_i, n_i : \Sigma_i \to \mathbb{R}$ (score functions under selection and under neutrality) with $s_i(y) > 0$ and $n_i(y) > 0$ for all $y$ (Grossman et al. 2010).

Conditionally on the hypothesis the components are modelled as independent, so joint scores are products. Only positivity is imposed; the posterior reading of the [normalized composite score](posterior.md) needs normalized score functions ([normalization](sum-joint-eq-one.md)).

## Sources

- S. R. Grossman, I. Shylakhter, E. K. Karlsson, E. H. Byrne, S. Morales, G. Frieden, E. Hostetter, E. Angelino, M. Garber, O. Zuk, E. S. Lander, S. F. Schaffner and P. C. Sabeti, *A composite of multiple signals distinguishes causal variants in regions of positive selection*, Science 327 (2010), 883–886.
