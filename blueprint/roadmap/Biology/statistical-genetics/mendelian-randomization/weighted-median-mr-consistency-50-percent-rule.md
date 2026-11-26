# Consistency of the weighted median MR estimator under 50% weight validity

Consider $J$ genetic instruments with ratio estimates $\hat\beta_j$ and normalized positive weights
$w_j$ ($\sum_{j=1}^J w_j = 1$) converging in probability to limiting positive weights $w_j^\infty$
with $\sum_{j=1}^J w_j^\infty = 1$ and $\max_j w_j^\infty < 1/2$. Let $V \subseteq \{1, \dots, J\}$
be the subset of valid instrumental variables (satisfying $\hat\beta_j \xrightarrow{p} \beta$ for
all $j \in V$).

If the valid instruments carry strictly more than half of the limiting weight,

$$\sum_{j \in V} w_j^\infty > \frac{1}{2},$$

then the [weighted median estimator](weighted-median-mr-estimator.md) is consistent for the causal effect:

$$\hat\beta_{\mathrm{WM}} \xrightarrow{p} \beta.$$

## Depends on

- [Weighted median Mendelian randomization estimator](weighted-median-mr-estimator.md)

## Expansion

For any $\varepsilon > 0$, with probability approaching $1$ all valid instruments $j \in V$ satisfy
$|\hat\beta_j - \beta| < \varepsilon$ and their combined weight satisfies $\sum_{j \in V} w_j > 1/2$.
Therefore, the cumulative weight of all estimates strictly below $\beta - \varepsilon$ is strictly less
than $1/2$, and the cumulative weight of all estimates at or below $\beta + \varepsilon$ is strictly
greater than $1/2$. Consequently, both neighboring order statistics bracketing the $50\%$ percentile
$p = 1/2$ lie in $(\beta - \varepsilon, \beta + \varepsilon)$, so their linear interpolation
$\hat\beta_{\mathrm{WM}}$ also lies in $(\beta - \varepsilon, \beta + \varepsilon)$.

## Sources

- J. Bowden, G. Davey Smith, P. C. Haycock, and S. Burgess, "Consistent Estimation in Mendelian Randomization with Some Invalid Instruments Using a Weighted Median Estimator", Genetic Epidemiology 40 (2016), 304–314, <https://doi.org/10.1002/gepi.21965> (PMC4849733).
