# Coloc prior elicitation and region-size dependence

In the single-causal-variant colocalization model for two traits on a region of $n$ SNPs, the per-SNP prior probabilities are $p_1$ (causal for trait 1 only), $p_2$ (trait 2 only) and $p_{12}$ (both traits). Write the marginal probabilities that a SNP is causal for each trait as

$$q_1 = p_1 + p_{12}, \qquad q_2 = p_2 + p_{12}.$$

**Region-size dependence.** The prior probabilities of the regional hypotheses are approximately $P(H_1) \approx n p_1$, $P(H_2) \approx n p_2$, $P(H_4) \approx n p_{12}$ (one shared causal variant) and $P(H_3) \approx n(n-1) p_1 p_2$ (two distinct causal variants). Hence the prior odds $H_4 : H_1$ equal $p_{12}/p_1$ for every $n$, while

$$\frac{P(H_4)}{P(H_3)} \approx \frac{p_{12}}{(n-1)\, p_1 p_2}$$

decreases in $n$: the same per-SNP priors favour distinct causal variants over colocalization as regions grow.

**Bounds on $p_{12}$.** Let $f$ be the proportion of variants that are functional and $r_g$ the genetic correlation of the two traits. If shared causal variants do not differ systematically in allele frequency or effect size from non-shared ones, then $|r_g| \le n_{12}/\sqrt{(n_{12} + n_1)(n_{12} + n_2)}$, where $n_{12}, n_1, n_2$ count shared and trait-specific causal variants, and therefore

$$\max\Bigl\{\frac{q_1 q_2}{f},\ |r_g| \sqrt{q_1 q_2}\Bigr\} < p_{12} < \min\{q_1, q_2\}.$$

Equivalently $p_{12} = q_{1|2}\, q_2$, where $q_{1|2}$ is the probability that a SNP causal for trait 2 is also causal for trait 1.

**Default values.** Empirical estimates from GTEx eQTL data and the GWAS Catalog, and the posterior obtained at $p < 5 \times 10^{-8}$, all support $q_1, q_2 \approx 10^{-4}$ for common SNPs; simulations indicate $p_{12} = 5 \times 10^{-6}$ is more robust than the older default $10^{-5}$, which can favour $H_4$ when $H_3$ is true.

## Depends on

- [The five colocalization hypotheses](coloc-hypothesis.md)
- [Colocalization prior parameters](coloc-prior.md)

## Expansion

$H_3$ and $H_4$ both put exactly one causal variant per trait in the region, but $H_3$ can be realized in $n(n-1)$ ordered ways and $H_4$ in only $n$, which explains the region-size effect. The lower bound $q_1q_2/f$ is the co-occurrence rate of independent traits once causality is known to imply functionality. The genetic-correlation bound treats $r_g$ as the overlap of the two causal sets, normalized by their sizes, which is proportional to $p_{12}/\sqrt{q_1 q_2}$. The upper bound states that joint causality cannot be more likely than causality for either trait alone.

## Sources

- C. Wallace, "Eliciting priors and relaxing the single causal variant assumption in colocalisation analyses", *PLoS Genetics* 16 (2020), e1008720, <https://doi.org/10.1371/journal.pgen.1008720> (PMC7192519; sections "The importance and elicitation of prior parameter values", "Marginal priors" and "Prior probability of joint or conditional causality"; derivations in S1 Text).
