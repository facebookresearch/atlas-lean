# Variance bound for exposure effects under misspecification

In the setting of [expected exposure effects](expected-exposure-effects-under-misspecified-exposure-mappings.md), assume bounded outcomes, $|y_i(z)| \le k_1$, and positivity for exposures $a$ and $b$, $1/\pi_i(d) \le k_2$ for all $i$ and $d \in \{a, b\}$. Define the design dependence and the error dependence of exposure $d$, with an absolute value around **each** term,

$$\bar c_d = \frac{1}{n^2} \sum_{i=1}^{n} \sum_{j \ne i} \bigl|\operatorname{cov}(D_{id}, D_{jd})\bigr|, \qquad \bar\varepsilon_d = \frac{1}{n^2} \sum_{i=1}^{n} \sum_{j \ne i} \bigl|\mathbb{E}(\varepsilon_i \varepsilon_j \mid D_i = D_j = d)\bigr|,$$

where $\varepsilon_i = y_i(Z) - \bar y_i(D_i)$, and a conditional expectation given $D_i = D_j = d$ is taken to be $0$ when $\Pr(D_i = D_j = d) = 0$. Both quantities are nonnegative. **Proposition.** The Horvitz–Thompson estimator satisfies

$$\operatorname{var}\{\hat\tau(a, b)\} \le \frac{8 k_1^2 k_2}{n} + 20 k_1^2 k_2^2 (\bar c_a + \bar c_b) + 4 (\bar\varepsilon_a + \bar\varepsilon_b).$$

Hence, if $\bar c_a, \bar c_b = o(1)$ and $\bar\varepsilon_a, \bar\varepsilon_b = o(1)$, then $\hat\tau(a, b) - \tau(a, b) \to 0$ in mean square, even though the exposures are misspecified.

## Depends on

- [Expected exposure effects under misspecified exposure mappings](expected-exposure-effects-under-misspecified-exposure-mappings.md)

## Expansion

All three terms are nonnegative; without the absolute values the signed off-diagonal averages can be negative and the right-hand side can fall below zero (for example, with exactly half of an even population treated and constant outcomes). They are the variability from randomly assigned exposures, from dependence between the exposures induced by the design, and from dependence between the specification errors. The size of the errors themselves enters only through boundedness; what matters for consistency is that they are weakly dependent on average, which the paper shows is implied by earlier conditions such as sparse interference with $d_{\mathrm{avg}} = o(n)$ or approximate neighbourhood interference. Unbiasedness and the bound together give convergence in mean square.

## Sources

- F. Sävje, *Causal inference with misspecified exposure mappings: separating definitions and assumptions*, Biometrika (2023). <https://doi.org/10.1093/biomet/asad019> Definition 3, Conditions 1–4 and Proposition 1 (Section 5).
