# Locus-level colocalization probability

Fix a candidate locus of $p$ SNPs, formed by intersecting a fine-mapping signal cluster (credible set) for a molecular trait, such as an eQTL, with one for a complex trait. Let $d \in \{0,1\}^p$ and $\gamma \in \{0,1\}^p$ be the latent causal indicators for the molecular and complex traits, with data $Y_e$ and $Y_g$ from non-overlapping samples. Let $D_k$ and $\Gamma_k$ be the configurations with exactly $k$ causal SNPs. By construction of signal clusters, at most one SNP in the locus is causal for each trait:

$$\Pr(d \in D_k \mid Y_e) = \Pr(\gamma \in \Gamma_k \mid Y_g) = 0 \qquad (k \ge 2).$$

The **locus-level colocalization probability** is the posterior probability that the locus contains a causal SNP for both traits, not necessarily the same one:

$$\mathrm{LCP} = \Pr(\gamma \in \Gamma_1, d \in D_1 \mid Y_g, Y_e) = \Pr(\gamma \in \Gamma_1 \mid d \in D_1, Y_g)\,\Pr(d \in D_1 \mid Y_e), \qquad \Pr(d \in D_1 \mid Y_e) = \sum_{i=1}^{p}\mathrm{PIP}^{e}_i .$$

**Computing the conditional factor.** Let $\pi_e = \Pr(\gamma_i = 1 \mid d_i = 1)$ and $\pi_{ne} = \Pr(\gamma_i = 1 \mid d_i = 0)$ be eQTL-informed priors, and let $\pi$ be the exchangeable prior used in the GWAS fine-mapping, so that $\Pr(\gamma \in \Gamma_1) = p\pi(1-\pi)^{p-1}$ and $\Pr(\gamma = 0) = (1-\pi)^p$. With $\Pr(\gamma \in \Gamma_1 \mid Y_g) = \sum_i \mathrm{PIP}^{g}_i =: S_g$, the locus Bayes factor is

$$\mathrm{BF} = \frac{\Pr(Y_g \mid \gamma \in \Gamma_1)}{\Pr(Y_g \mid \gamma = 0)} = \frac{S_g}{1 - S_g}\cdot\frac{1-\pi}{p\pi}.$$

Given a single eQTL SNP in the locus, the prior odds of one GWAS signal against none are

$$O = \frac{\Pr(\gamma \in \Gamma_1 \mid d \in D_1)}{\Pr(\gamma = 0 \mid d \in D_1)} = \frac{\pi_e}{1 - \pi_e} + (p-1)\frac{\pi_{ne}}{1 - \pi_{ne}},$$

and Bayes' theorem gives

$$\Pr(\gamma \in \Gamma_1 \mid d \in D_1, Y_g) = \frac{O\cdot\mathrm{BF}}{1 + O\cdot\mathrm{BF}}.$$

Because LCP also counts distinct causal variants for the two traits within the same locus, $\mathrm{LCP} \ge \mathrm{RCP}$, the regional probability of a single shared causal variant. Gene-level summaries combine independent signals $r$ or loci $l$ of a gene–tissue pair $G_t$:

$$\mathrm{GRCP}_{G_t} = 1 - \prod_{r \in G_t}(1 - \mathrm{RCP}_r), \qquad \mathrm{GLCP}_{G_t} = 1 - \prod_{l \in G_t}(1 - \mathrm{LCP}_l).$$

## Depends on

- [Posterior inclusion probability](pip.md)
## Expansion

With at most one causal SNP per trait, the events "SNP $i$ is causal" are disjoint, so $\Pr(d \in D_1 \mid Y_e)$ is the sum of the PIPs; the same holds for $S_g$. The factorization uses the independence of the two samples. The BF is posterior odds divided by the prior odds $p\pi(1-\pi)^{p-1}/(1-\pi)^p$ under the eQTL-agnostic prior. Under the eQTL-informed prior, given that SNP $i$ is the eQTL, exactly one GWAS signal arises either at $i$, with weight $\pi_e(1-\pi_{ne})^{p-1}$, or at one of the other $p - 1$ SNPs, with weight $(p-1)\pi_{ne}(1-\pi_e)(1-\pi_{ne})^{p-2}$. No GWAS signal has weight $(1-\pi_e)(1-\pi_{ne})^{p-1}$. The paper writes these with a common factor $p$ (summing over the eQTL position), which cancels in $O$. The gene-level formulas give the probability that at least one of several independent signals colocalizes. The paper shows that genes with strong TWAS but weak variant-level colocalization are largely reconciled by LCP, whereas genes with strong colocalization but weak TWAS evidence are complementary.

## Sources

- A. Hukku, M. G. Sampson, F. Luca et al., "Analyzing and reconciling colocalization and transcriptome-wide association studies from the perspective of inferential reproducibility", *American Journal of Human Genetics* 109(5) (2022), 825–837, <https://doi.org/10.1016/j.ajhg.2022.04.005> (PMC9118134), Material and methods (Equation 1 and "Probabilistic colocalization analysis at the locus level", Equations 2–12) and Results.
