# Conditional likelihood for matched case–control sets with several cases

Suppose stratum $i$ consists of $m$ observations with labels $Y_{i\ell} \in \{0, 1\}$ (case status) and predictors $X_{i\ell}$, and given the predictors $X_{i1}, \dots, X_{im}$ and the stratum intercept $\alpha_i$ the labels $Y_{i1}, \dots, Y_{im}$ are conditionally independent Bernoulli variables with $P(Y_{i\ell} = 1 \mid X_{i\ell}) = \operatorname{expit}(\alpha_i + \beta^\top X_{i\ell})$, the logistic model with a stratum-specific intercept; strata are independent. Conditioning on the number $k$ of cases in each stratum removes the intercepts: with the first $k$ observations the cases,

$$P\Bigl(Y_{ij} = 1 \text{ for } j \le k,\ Y_{ij} = 0 \text{ for } k < j \le m \Bigm| X_{i1}, \dots, X_{im},\ \sum_j Y_{ij} = k\Bigr) = \frac{\exp\bigl(\sum_{j=1}^k \beta^\top X_{ij}\bigr)}{\sum_{J \in \mathcal C_k^m} \exp\bigl(\sum_{j \in J} \beta^\top X_{ij}\bigr)},$$

where $\mathcal C_k^m$ is the set of $k$-element subsets of $\{1, \dots, m\}$, and the conditional log-likelihood is the sum over strata. This log-likelihood has the form of a Cox partial likelihood with a particular data structure (Prentice and Breslow 1978). The case of one case per set ($k = 1$) is [the conditional probability is free of the intercept](../../../not-yet-classified/conditional-logistic-matched-sets/conditional-case-prob-eq.md), with the product over sets in [two forms of the conditional likelihood of independent matched sets](../../../not-yet-classified/conditional-logistic-matched-sets/prod-conditional-likelihood-eq.md); the 1:1 binary-exposure estimator $n_{10}/n_{01}$ is [the conditional MLE for 1:1 matching](../../../not-yet-classified/conditional-logistic-matched-sets/paired-conditional-log-lik-max.md), and the squared estimate of the analysis with one intercept per pair is [the maximizer of the incidental-parameter log-likelihood](../../../not-yet-classified/conditional-logistic-matched-sets/per-pair-intercept-log-lik-le.md) (Breslow and Day 1980, Section 7.1).

## Expansion

1. The model: matched sets with $k$ cases, stratum-specific intercepts, and the conditioning event.
2. The conditional probability of the observed case configuration given the number $k$ of cases, and the cancellation of $\alpha_i$ for general $k$.
3. The equivalence with a stratified Cox partial likelihood.
4. The inconsistency of the unconditional estimator with one intercept per pair, whose odds-ratio estimate tends to the square of the true one, in the spirit of the Neyman–Scott incidental-parameter inconsistency of maximum likelihood, as a separate statement.

## Sources

- N. E. Breslow and N. E. Day, *Statistical Methods in Cancer Research, Vol. I: The Analysis of Case–Control Studies*, IARC Sci. Publ. 32, International Agency for Research on Cancer, Lyon, 1980, Chapter 7.
- R. L. Prentice and N. E. Breslow, Retrospective studies and failure time models, Biometrika 65 (1978), 153–158. <https://doi.org/10.1093/biomet/65.1.153>
