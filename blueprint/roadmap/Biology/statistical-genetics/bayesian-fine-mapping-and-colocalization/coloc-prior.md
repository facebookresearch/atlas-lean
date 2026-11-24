# Colocalization prior parameters

Let $\iota$ be a finite set of $m$ variants. Colocalization prior parameters on $\iota$ are real numbers $p_1, p_2, p_{12} \ge 0$ (the weights of a variant being causal for trait 1 only, trait 2 only, and both traits) such that

$$m\, p_1 + m\, p_2 + m (m - 1)\, p_1 p_2 + m\, p_{12} \le 1.$$

The bound leaves nonnegative null mass for the separate normalized [categorical prior](categorical-prior.md); the unnormalized configuration weights of Giambartolomei et al. (2014) give the null configuration weight $1$.

## Sources

- C. Giambartolomei et al., *Bayesian test for colocalisation between pairs of genetic association studies using summary statistics*, PLoS Genet. 10 (2014), e1004383.
