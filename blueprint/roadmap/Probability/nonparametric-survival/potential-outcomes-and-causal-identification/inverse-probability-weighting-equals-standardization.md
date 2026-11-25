# Inverse probability weighting equals standardization

Let $\mu$ be a probability measure, $T$ a measurable event, $X$ a measurable covariate with values in a finite set, $e(x) = \mu(T \mid X = x)$ the propensity score, and $Y$ an integrable observed outcome. Suppose positivity: $e(x) > 0$ whenever $\mu(X = x) > 0$. Then $\mathbb{E}[\mathbf 1_T\,Y/e(X)] = \sum_{x : \mu(X = x) > 0} \mu(X = x)\,\mathbb{E}[Y \mid T, X = x]$, where the integrand is defined almost surely: the inverse-probability-weighted mean equals the standardized mean. The identity concerns only the observed law; under strong ignorability both equal the counterfactual mean, as on the inverse-probability-weighting pages.

Proof. Split the expectation over the events $\{X = x\}$ of positive probability. On $\{X = x\}$ the weight is the constant $1/e(x)$, and $\mathbb{E}[\mathbf 1_T Y \mathbf 1_{\{X = x\}}] = \mu(T \cap \{X = x\})\,\mathbb{E}[Y \mid T, X = x] = e(x)\,\mu(X = x)\,\mathbb{E}[Y \mid T, X = x]$, so the factor $e(x)$ cancels.

## Depends on

- [Propensity score](propensity.md): the propensity score.

## Background

- [Inverse probability weighting for the treated mean](integral-ipw-treated.md): identification of the treated mean by inverse probability weighting.

## Sources

- M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman & Hall/CRC, 2020, <https://miguelhernan.org/whatifbook>, Technical Point 2.3 (equivalence of IP weighting and standardization)
