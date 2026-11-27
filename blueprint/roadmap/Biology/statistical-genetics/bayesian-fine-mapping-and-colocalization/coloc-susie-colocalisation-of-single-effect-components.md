# coloc-SuSiE: colocalisation of pairs of single-effect components

Let two traits be measured on a common region of $J$ variants with GWAS summary statistics and an LD matrix $R$. Classical **coloc** assumes at most one causal variant per trait in the region; then each pair (causal variant for trait 1 or none, causal variant for trait 2 or none) belongs to exactly one of the global hypotheses
$H_0$ (no association), $H_1$ (trait 1 only), $H_2$ (trait 2 only), $H_3$ (both associated, distinct causal variants), $H_4$ (both associated, one shared causal variant), and with per-variant Bayes factors $\mathrm{BF}^{(1)}_j, \mathrm{BF}^{(2)}_j$ and priors $p_1, p_2, p_{12}$ the hypothesis weights are

$$C(H_1) = p_1 \textstyle\sum_j \mathrm{BF}^{(1)}_j,\quad C(H_3) = p_1 p_2 \Big(\sum_j \mathrm{BF}^{(1)}_j \sum_k \mathrm{BF}^{(2)}_k - \sum_j \mathrm{BF}^{(1)}_j \mathrm{BF}^{(2)}_j\Big),\quad C(H_4) = p_{12} \textstyle\sum_j \mathrm{BF}^{(1)}_j \mathrm{BF}^{(2)}_j,$$

analogously for $H_0, H_2$, normalized to posterior probabilities.

**coloc-SuSiE.** Fit the Sum of Single Effects model $b = \sum_{l=1}^{L} b_l$, each $b_l$ having exactly one nonzero coordinate at an unknown position, to each trait from summary statistics (SuSiE-RSS). For trait $t$ this yields, for every single-effect component $l$, a vector of variant-level Bayes factors $\big(\mathrm{BF}^{(t,l)}_j\big)_{j=1}^{J}$, and a list of the $L_t$ components for which a 95% credible set is formed. For every pair $(l_1, l_2)$ of credible-set components, run the single-causal-variant coloc computation with $\mathrm{BF}^{(1)} = \mathrm{BF}^{(1,l_1)}$ and $\mathrm{BF}^{(2)} = \mathrm{BF}^{(2,l_2)}$. The output is an $L_1 \times L_2$ matrix of posterior probabilities $\Pr(H_4 \mid \text{data}; l_1, l_2)$; a large entry indicates that signal $l_1$ of trait 1 and signal $l_2$ of trait 2 share a causal variant.

## Depends on

- [Closed-form colocalization hypothesis scores](coloc-closed-form.md)
- [Sum of Single Effects (SuSiE) model and factored variational family](../sum-of-single-effects-susie/sum-of-single-effects-model.md)
## Expansion

The single-causal-variant assumption is what makes the variant-level events "variant $j$ is causal" mutually exclusive, so that log Bayes factors of global hypotheses are log-sums of variant-level ones. Marginal posterior inclusion probabilities from multi-variant fine-mapping are not mutually exclusive, so they cannot be plugged into coloc directly. Within one SuSiE single-effect component, however, exactly one variant is causal, so the component's variant-level Bayes factors again describe mutually exclusive events and coloc applies to each pair of components unchanged. This replaces the earlier conditional-regression approach, which peels off signals by stepwise conditioning and can mislabel weaker secondary signals. In simulations with one or two causal variants per trait, coloc-SuSiE matched single-variant coloc when there was one causal variant and was more accurate than conditioning when there were two. It runs fewer comparisons when SuSiE finds no credible set for a trait, which mostly happens at low power.

## Sources

- C. Wallace, "A more accurate method for colocalisation analysis allowing for multiple causal variants", PLoS Genetics 17 (2021), e1009440, Introduction and Methods ("Adaptation of coloc approach"), <https://doi.org/10.1371/journal.pgen.1009440> (PMC8504726).
- C. Giambartolomei et al., "Bayesian test for colocalisation between pairs of genetic association studies using summary statistics", PLoS Genetics 10 (2014), e1004383, <https://doi.org/10.1371/journal.pgen.1004383>.
