# Quadratic-approximation estimator of the selection gradient

In the [composite likelihood for the selection gradient](composite-likelihood-for-the-selection-gradient-from-snp-likelihoods.md) with one SNP per linkage-disequilibrium block, approximate each SNP log-likelihood ratio near its maximizer by a quadratic, $\log \widehat{LR}_i(s) \approx a_i s^2 + b_i s + c_i$. Then

$$\log \widehat{LR}(\omega) \approx \sum_{i=1}^{M} \Bigl(a_i \bigl(\beta^{(i)\top} \omega\bigr)^2 + b_i\, \beta^{(i)\top} \omega + c_i\Bigr),$$

and, when $A = \sum_i a_i \beta^{(i)} \beta^{(i)\top}$ is negative definite, its unique maximizer solves the linear system $2 A \omega = -\sum_i b_i \beta^{(i)}$:

$$\hat\omega = -\Bigl[2 \sum_{i=1}^{M} a_i\, \beta^{(i)} \beta^{(i)\top}\Bigr]^{-1} \sum_{i=1}^{M} b_i\, \beta^{(i)}.$$

Standard errors come from a block bootstrap over linkage-disequilibrium blocks, and $\hat\omega / \widehat{\mathrm{se}}$ is used as a Wald statistic.

## Depends on

- [Composite likelihood for the selection gradient from SNP likelihoods](composite-likelihood-for-the-selection-gradient-from-snp-likelihoods.md)

## Proof depends on

- [Composite likelihood for the selection gradient from SNP likelihoods](composite-likelihood-for-the-selection-gradient-from-snp-likelihoods.md)

## Expansion

The approximated objective is a quadratic form in $\omega$ with Hessian $2A$; setting its gradient $2A\omega + \sum_i b_i \beta^{(i)}$ to zero gives $\hat\omega$, and negative definiteness of $A$ makes the stationary point the maximum. The closed form makes the estimate cheap enough to bootstrap. The sign in front of the bracket follows from this derivation; the estimator corresponds to the paper's Equation A7.

## Sources

- A. J. Stern et al., *Disentangling selection on genetically correlated polygenic traits via whole-genome genealogies*, Am. J. Hum. Genet. 108 (2021). <https://doi.org/10.1016/j.ajhg.2020.12.005> (PMCID: PMC7895848) Appendix A, Equations A6 and A7, and "Selection gradient and correlated selection standard errors".
