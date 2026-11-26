# Inverse probability weighting equals standardization

Let $\mu$ be a probability measure, $T$ a measurable event, $X$ a measurable covariate with values in a finite set, and $Y$ an integrable observed outcome. Let $e(x)=\mu(T\mid X=x)$ be the [propensity score](propensity.md) and suppose $e(x)>0$ whenever $\mu(X=x)>0$. Then the weighted outcome $\mathbf 1_T\,Y/e(X)$ is integrable and

$$\mathbb E[\mathbf 1_T\,Y/e(X)] = \sum_{x:\,\mu(X=x)>0} \mu(X=x)\,\mathbb E[Y\mid T,X=x].$$

The right side is the standardized mean. The same sum can include every stratum, with each null stratum contributing zero. On null strata the weighted outcome is defined to be zero. This identity concerns only the observed law: it does not require conditional exchangeability and allows $e(x)=1$. If treatment is strongly ignorable given $X$ for an integrable treated potential outcome $Y(1)$, and $Y=Y(1)$ almost surely on $T$ (consistency), the common value is also the counterfactual mean $\mathbb E[Y(1)]$, as on the inverse-probability-weighting page.

Proof. Split the expectation over the finitely many events $\{X=x\}$. On a stratum of positive probability, the weight is the constant $1/e(x)$ and the integral of $\mathbf 1_T Y$ over the stratum is $e(x)\,\mu(X=x)\,\mathbb E[Y\mid T,X=x]$. Cancel $e(x)$ and sum. Null strata do not affect the integral.

## Background

- [Inverse probability weighting for the treated mean](integral-ipw-treated.md): identification of the treated mean by inverse probability weighting.

## Sources

- M. A. Hernán and J. M. Robins, *Causal Inference: What If*, Chapman & Hall/CRC, 2020, <https://miguelhernan.org/whatifbook>, Technical Point 2.3 (equivalence of IP weighting and standardization)
