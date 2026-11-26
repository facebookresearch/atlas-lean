# Multi-ethnic polygenic risk score

Let $\hat b_i^{(P)}$, $i=1,\dots,M$, be marginal GWAS effect estimates from a training population $P$, and let $\mathcal S_P(R^2_{LD},P_T)$ be the set of SNPs kept by LD-clumping at pairwise threshold $R^2_{LD}$ followed by a $p$-value threshold $P_T$. The pruning-and-thresholding polygenic risk score of an individual with genotypes $g_i$ is

$$\mathrm{PRS}_P=\sum_{i\in\mathcal S_P(R^2_{LD},P_T)}\hat b_i^{(P)}g_i .$$

Given scores built from two training populations, for example a large European sample and a smaller sample matching the target population, the **multi-ethnic PRS** with mixing weights $\alpha_1,\alpha_2$ is

$$\mathrm{PRS}_{1+2}=\alpha_1\mathrm{PRS}_1+\alpha_2\mathrm{PRS}_2,$$

optionally extended by an ancestry predictor, $\alpha_1\mathrm{PRS}_1+\alpha_2\mathrm{PRS}_2+\alpha_3\,\mathrm{PC}_1$. The weights are fitted by regressing the phenotype on the component scores in validation data from the target population, and accuracy is reported as adjusted

$$R^2_{\mathrm{adj}}=\hat R^2-(1-\hat R^2)\frac{p}{n-p-1},$$

with $p\in\{1,2,3\}$ the number of components and $n$ the validation sample size (on the liability scale for binary traits), or by cross-validation of the weights.

## Expansion

Because $\mathrm{PRS}_1$ and $\mathrm{PRS}_2$ are fixed linear predictors, choosing $(\alpha_1,\alpha_2)$ by least squares on validation data can only raise in-sample $R^2$ relative to either score alone; the adjusted $R^2$ (or cross-validation) charges for the extra fitted weight. The gain comes from complementary information: the large external sample gives precise effect estimates, the target-population sample matches its LD and allele frequencies. The clumping and threshold parameters are tuned on each single-population score, so the combination gets no advantage from that tuning. A Bayesian alternative that couples effect sizes across populations is the PRS-CSx shrinkage prior.

## Sources

- C. Márquez-Luna, P.-R. Loh, A. L. Price et al., *Multiethnic polygenic risk scores improve risk prediction in diverse populations*, Genetic Epidemiology 41 (2017), 811–823, <https://doi.org/10.1002/gepi.22083> (PMCID: PMC5726434). Materials and Methods, "Polygenic risk score using one training population", "Polygenic risk score using two training populations", "Polygenic risk score using one or two training populations and genetic ancestry" and "Assessment of methods".
