# Dominance and interaction logistic models for multi-allelic loci

At a locus with $m$ alleles or haplotypes, let $x_{i,j} \in [0, 2]$ be the dosage of allele $j$ in individual $i$ and let $C_i$ collect the covariate terms (cohort indicators, principal components, sex). Consider the nested logistic models

$$\text{additive:}\quad \log(\mathrm{odds}_i) = \theta + \sum_{j=1}^{m-1} a_j x_{i,j} + C_i,$$

$$\text{dominance:}\quad \log(\mathrm{odds}_i) = \theta + \sum_{j=1}^{m-1} a_j x_{i,j} + \sum_{j=1}^{m} d_j\, \delta_{i,j} + C_i,$$

$$\text{interaction:}\quad \log(\mathrm{odds}_i) = \theta + \sum_{j=1}^{m-1} a_j x_{i,j} + \sum_{j=1}^{m} \sum_{h=j+1}^{m} \phi_{j,h}\, x_{i,j} x_{i,h} + C_i,$$

where allele $m$ is the reference, $\delta_{i,j} = 1 - |1 - x_{i,j}|$ is the heterozygosity indicator for allele $j$ (equal to $1$ exactly when $x_{i,j} = 1$ for hard calls), $d_j$ is the dominance effect and $\phi_{j,h}$ the interaction effect. On the log-odds scale a heterozygote for allele $j$ has effect $a_j + d_j$ and a homozygote $2a_j$. Models are compared by the deviance change $-2(\ell_0 - \ell_1)$, referred to a $\chi^2$ law whose degrees of freedom equal the number of added parameters: $m$ for dominance over additive, and $m(m-1)/2 - m$ for interaction over dominance.

## Expansion

Departure from additivity ($d_j \neq 0$) means the second copy of an allele changes risk by a different amount than the first. Pairwise interactions between two different alleles in a heterozygote can masquerade as dominance at individual alleles, since every heterozygote for $j$ carries some other allele $h$; when the interaction model fits better than the dominance model, the non-additivity is explained by specific allele pairs. The total odds ratio of a genotype carrying alleles $j$ and $h$ is the product of the two additive odds ratios and the interaction odds ratio $e^{\phi_{j,h}}$. In five autoimmune diseases the source found significant dominance in four and, for rheumatoid arthritis, type 1 diabetes and celiac disease, pairwise interactions explaining it; imputation artifacts were excluded by permuting genotypes under the fitted additive model. Imputation quality was summarized by $\mathrm{INFO} = \operatorname{var}(x)/(2p(1-p))$ for an allele of frequency $p$.

## Sources

- T. L. Lenz, A. J. Deutsch, B. Han, X. Hu, Y. Okada, S. Eyre, et al., "Widespread non-additive and interaction effects within HLA loci modulate the risk of autoimmune diseases", *Nature Genetics* 47 (2015), 1085–1090, Online Methods Equations 1–4, <https://doi.org/10.1038/ng.3379> (PMC4552599).
