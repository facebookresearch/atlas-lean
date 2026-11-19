# Closed-form colocalization hypothesis scores

Let $p_1, p_2, p_{12}$ be [colocalization prior parameters](coloc-prior.md) on a finite set $\iota$ of variants, and let $\mathrm{BF}^{(1)}, \mathrm{BF}^{(2)} : \iota \to \mathbb{R}$ be arbitrary. The closed-form scores of the five [colocalization hypotheses](coloc-hypothesis.md) are

- $C(H_0) = 1$;
- $C(H_1) = p_1 \sum_j \mathrm{BF}^{(1)}_j$;
- $C(H_2) = p_2 \sum_k \mathrm{BF}^{(2)}_k$;
- $C(H_3) = p_1 p_2 \bigl(\sum_j \mathrm{BF}^{(1)}_j \sum_k \mathrm{BF}^{(2)}_k - \sum_j \mathrm{BF}^{(1)}_j \mathrm{BF}^{(2)}_j\bigr)$;
- $C(H_4) = p_{12} \sum_j \mathrm{BF}^{(1)}_j \mathrm{BF}^{(2)}_j$,

all sums over $\iota$. These are the formulas of Giambartolomei et al. (2014); for nonnegative Bayes factors they are unnormalized hypothesis weights.

## Sources

- C. Giambartolomei et al., *Bayesian test for colocalisation between pairs of genetic association studies using summary statistics*, PLoS Genet. 10 (2014), e1004383.
