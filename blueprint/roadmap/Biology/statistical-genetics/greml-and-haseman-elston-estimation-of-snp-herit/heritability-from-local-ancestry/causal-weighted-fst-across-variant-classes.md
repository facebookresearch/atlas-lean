# Causal-variant $F_{ST}$ as a heritability-weighted average over variant classes

In the setting of the [local-ancestry heritability identity](local-ancestry-heritability-identity.md), partition the SNPs into disjoint classes $L$ (for example rare and common variants) and let $h_L^2 = \sum_{s \in L} \beta_s^2$, so that $h^2 = \sum_L h_L^2$. Define the class-specific differentiation

$$F_{ST}^{L} = \sum_{s \in L} \frac{\beta_s^2}{h_L^2}\, \frac{(p_{s,1} - p_{s,0})^2}{\sigma_{g,s}^2}.$$

Then

$$F_{STC} = \sum_L \frac{h_L^2}{h^2}\, F_{ST}^{L},$$

and under the hypotheses of the exact identity (constant global ancestry $\theta_i \equiv \theta$ and uncorrelated local ancestries at distinct causal SNPs)

$$h_\gamma^2 = 2\theta(1-\theta)\, h^2 \sum_L \frac{h_L^2}{h^2} F_{ST}^{L};$$

when global ancestry varies this is the plug-in approximation of that page.

If within each class the effect sizes are independent of the ancestral allele frequencies, $F_{ST}^{L}$ equals the class average $\mathbb{E}_{s \in L}\big[(p_{s,1}-p_{s,0})^2/\sigma_{g,s}^2\big]$; with a single class (the infinitesimal model) this is the average-of-ratios $F_{ST} = \mathbb{E}_s\big[(p_{s,1}-p_{s,0})^2/\sigma_{g,s}^2\big]$.

## Depends on

- [Heritability explained by local ancestry in a two-way admixed population](local-ancestry-heritability-identity.md)

## Expansion

The identity is a regrouping of the sum defining $F_{STC}$ by class. It matters because average-of-ratios $F_{ST}$ shrinks when many rare variants are included, so the value of $F_{STC}$, and hence the plug-in estimate $h^2 \approx h_\gamma^2/(2\theta(1-\theta) F_{STC})$, depends on how heritability is split across frequency classes: with class values $0.054$ (rare) and $0.182$ (common) and $10\%/90\%$ of heritability in the two classes, $F_{STC} = 0.1 \cdot 0.054 + 0.9 \cdot 0.182 = 0.1692$. Using a wrong $F_{STC}$ scales the heritability estimate by the ratio of the true to the assumed value, and positive selection at a highly differentiated causal locus (for example the Duffy-null allele for white blood cell count) inflates $F_{STC}$ for that trait; conditioning on ancestry at such a locus as a fixed effect removes the bias.

## Sources

- N. Zaitlen, B. Pasaniuc, S. Sankararaman et al., "Leveraging population admixture to characterize the heritability of complex traits", Nature Genetics 46 (2014), <https://doi.org/10.1038/ng.3139> (PMC4244251). Online Methods, Equations (1)-(15); Eq. (4) is stated there as an approximation.
