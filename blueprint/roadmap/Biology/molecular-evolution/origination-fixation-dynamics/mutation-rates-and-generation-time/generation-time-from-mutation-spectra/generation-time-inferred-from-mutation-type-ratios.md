# Generation time inferred from mutation-type ratios

Model the expected number of de novo mutations of type $k$ that a child inherits from a parent as linear in that parent's age at conception: $\beta_p^k G_p + \alpha_p^k$ from a father of age $G_p$ and $\beta_m^k G_m + \alpha_m^k$ from a mother of age $G_m$, with observed counts Poisson with these means (slopes $\beta$ and intercepts $\alpha$ estimated by maximum likelihood from parent–offspring trios). For two mutation types $1, 2$ the expected ratio of their counts per generation is

$$\rho_{1,2}(G_p, G_m) = \frac{(\beta_p^1 G_p + \alpha_p^1) + (\beta_m^1 G_m + \alpha_m^1)}{(\beta_p^2 G_p + \alpha_p^2) + (\beta_m^2 G_m + \alpha_m^2)} .$$

Given an observed ratio $R$ of the two types among polymorphisms that arose in some past time window, the parental ages compatible with it satisfy $\rho_{1,2}(G_p, G_m) = R$, which, for positive denominator, is the **linear** constraint

$$(\beta_p^1 - R\beta_p^2)\,G_p + (\beta_m^1 - R\beta_m^2)\,G_m = R(\alpha_p^2 + \alpha_m^2) - (\alpha_p^1 + \alpha_m^1).$$

If paternal and maternal ages co-vary with a fixed ratio $G_p / G_m = \gamma$, the constraint has the unique solution

$$G_m = \frac{R(\alpha_p^2 + \alpha_m^2) - (\alpha_p^1 + \alpha_m^1)}{\gamma(\beta_p^1 - R\beta_p^2) + (\beta_m^1 - R\beta_m^2)}, \qquad G_p = \gamma G_m,$$

whenever the denominator is nonzero. A change in generation time alone moves all ratios along one curve in $(G_p, G_m)$; observed ratios of different mutation types that imply incompatible ages, or ages outside a plausible human range, cannot be explained by generation-time change alone.

## Depends on

- [Mean of the Poisson distribution](../../../../population-genetics/haldane-s-survival-probability-of-a-beneficial-m/mean-poisson-measure.md)

## Expansion

Cross-multiplying the ratio equation by its positive denominator gives the linear constraint, a line in the $(G_p, G_m)$ plane, and intersecting with the ray $G_p = \gamma G_m$ gives the closed form. Each pairwise ratio is a monotone function of the ages along any such ray, so its observed value pins down one age. Gao et al. estimated the parental-age effects from de novo mutations in Icelandic trios (for example, if both parents reproduce at $40$ rather than $20$ years, the non-CpG C>T/C>A and non-TpG T>C/T>G ratios fall by $9.4\%$ and $7.5\%$ while C>G/T>A rises by $11.9\%$), took ratios of polymorphisms in age bins of the 1000 Genomes CEU sample, and solved these equations for $\gamma \in \{0.8, 1, 1.1, 1.2\}$, propagating uncertainty by bootstrap resampling of trios. The implied ages were mutually inconsistent across mutation types: the T>C/T>G ratio required generation times above $40$ years, while the peak of the C>T/C>A ratio around $238$–$887$ generations ago required average reproductive ages below $20$ years. They conclude that plausible changes in generation time cannot jointly explain the evolution of the human mutation spectrum, leaving a role for genetic modifiers or environmental exposures.

## Sources

- Z. Gao, Y. Zhang, N. Cramer, M. Przeworski, P. Moorjani, "Limited role of generation time changes in driving the evolution of the mutation spectrum in humans", eLife 12 (2023), e81188, <https://doi.org/10.7554/eLife.81188> (PMC10014080), Results (Figures 3–4) and Methods, "Estimation of parental age effects on DNM counts and ratios" and "Inference of generation time corresponding to the observed polymorphism ratios".
