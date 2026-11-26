# Local-ancestry mixture model for a dominant causal allele

**Model.** Individuals of a two-way admixed population have $k \in \{0, 1, 2\}$ copies of ancestry from source $E$ at a locus (and $2 - k$ from source $A$). A biallelic causal variant has allele $H$ at frequency $P_E$ on $E$-ancestry haplotypes and $P_A$ on $A$-ancestry haplotypes, and each haplotype carries $H$ independently given its ancestry. The phenotype $Y$ is normal with mean $\mu_H$ and standard deviation $\sigma_H$ in carriers of at least one $H$ allele (dominance) and with mean $\mu_L$ and standard deviation $\sigma_L$ in non-carriers.

**Proposition.** Given local ancestry $k$, the carrier probability is

$$c_k(P_E, P_A) = 1 - (1 - P_E)^{k}(1 - P_A)^{2-k},$$

and $Y$ has the two-component normal mixture density

$$g_k(y) = c_k\,\varphi(y; \mu_H, \sigma_H) + (1 - c_k)\,\varphi(y; \mu_L, \sigma_L).$$

For independent individuals with observed $(k_n, y_n)$ the likelihood of the six parameters $(P_E, P_A, \mu_H, \sigma_H, \mu_L, \sigma_L)$ is $\prod_n g_{k_n}(y_n)$. In particular

$$\mathbb E[Y \mid k = 2] - \mathbb E[Y \mid k = 0] = (\mu_H - \mu_L)\bigl[(1 - P_A)^2 - (1 - P_E)^2\bigr] = (\mu_H - \mu_L)(P_E - P_A)(2 - P_E - P_A).$$

The contrast vanishes when $\mu_H = \mu_L$, whatever the allele frequencies, so its size says nothing about $P_E - P_A$ until the effect $\mu_H - \mu_L$ is pinned down. Since $0 \le 2 - P_E - P_A \le 2$, the contrast is at most $2\,|\mu_H - \mu_L|\,|P_E - P_A|$ in absolute value; when the mixture separates the two components, so that $\mu_H - \mu_L$ is estimated from the within-class distributions, an ancestry contrast close to $\mu_H - \mu_L$ forces $P_E - P_A$ to be large. Profiling the likelihood over a grid of $P_A$ (or $P_E$) with the other parameters maximized gives marginal likelihood curves and hence bounds on the causal allele's frequencies in the source populations.

**Use.** Applied to neutrophil counts in African Americans, local ancestry at chromosome 1q23 implied that the allele raising neutrophil count has frequency below $4.9\%$ in Africans and above $95.2\%$ in Europeans, a differentiation above $91.9\%$; only a handful of known SNPs in the admixture peak are that differentiated, which prioritized the Duffy-null variant.

## Expansion

A non-carrier must have the non-$H$ allele on each of its two haplotypes; by independence this has probability $(1 - P_E)^k(1 - P_A)^{2-k}$, and $c_k$ is its complement. Conditioning on carrier status gives the mixture. The mean difference follows from $\mathbb E[Y \mid k] = \mu_L + c_k(\mu_H - \mu_L)$ and $c_2 - c_0 = (1 - P_A)^2 - (1 - P_E)^2$; the effect size $\mu_H - \mu_L$ multiplies the whole contrast. If $P_E$ and $P_A$ were close, the three ancestry classes would have nearly equal mixture weights and their phenotype distributions would be nearly identical; the observed dominant pattern (classes $k = 1$ and $k = 2$ alike, class $k = 0$ different) is reproduced only when $c_1 \approx c_2 \approx 1$ and $c_0 \approx 0$, i.e. $P_E \approx 1$ and $P_A \approx 0$.

## Sources

- D. Reich, M. A. Nalls, W. H. L. Kao, E. L. Akylbekova, A. Tandon, N. Patterson, J. Mullikin, W.-C. Hsueh, C.-Y. Cheng, J. Coresh, E. Boerwinkle, et al., *Reduced neutrophil count in people of African descent is due to a regulatory variant in the Duffy antigen receptor for chemokines gene*, PLoS Genetics 5 (2009), e1000360, <https://doi.org/10.1371/journal.pgen.1000360>, PMCID PMC2628742. Results, "The Causal Allele must be >91% Differentiated between Africans and Europeans" (six-parameter model, likelihood over 6,005 individuals, bounds $P_A < 4.9\%$, $P_E > 95.2\%$), and Figure 1. The carrier probability and mean-difference identity are derived here from the stated model.
