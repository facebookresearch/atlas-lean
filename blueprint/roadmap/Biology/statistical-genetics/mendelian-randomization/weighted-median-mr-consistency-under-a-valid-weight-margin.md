# Consistency of the weighted median MR estimator under a valid-weight margin

Fix $J \ge 1$ genetic variants. For each sample size $N$, let $\hat\beta_{j}$ be the ratio estimate of variant
$j$ and $w_j > 0$ its normalized weight ($\sum_{j=1}^J w_j = 1$), all depending on $N$, and let
$\hat\beta_{\mathrm{WM}}$ be the [interpolated weighted median estimator](weighted-median-mr-estimator.md)
computed from them. Suppose that, as $N \to \infty$, $w_j \xrightarrow{p} w_j^\infty$ for every $j$, where
$w_j^\infty \ge 0$ are constants with $\sum_{j=1}^J w_j^\infty = 1$, and let
$V \subseteq \{1, \dots, J\}$ be a set of valid instruments: $\hat\beta_j \xrightarrow{p} \beta$ for every
$j \in V$, while the estimates of the variants outside $V$ are arbitrary.

If the valid instruments carry a limiting weight

$$\sum_{j \in V} w_j^\infty > \frac{1 + \max_{1 \le j \le J} w_j^\infty}{2},$$

then $\hat\beta_{\mathrm{WM}} \xrightarrow{p} \beta$.

A strict majority of valid weight, $\sum_{j \in V} w_j^\infty > 1/2$, does not suffice for the interpolated
estimator. Bowden et al. (2016), Web Appendix 1, already distinguish the empirical weighted median from the
mid-point interpolated one, give a counterexample to consistency under a valid-weight majority alone for the
latter, and give a guarantee when no variant carries more than 10% of the weight and at least 55% of it is valid.
The margin $\sum_{j \in V} w_j^\infty > (1 + \max_j w_j^\infty)/2$ above is a general sufficient condition
derived on this page; it is not necessary for every configuration. With true effect $0$, estimates $(-1, 0, 1/N)$ and weights $(0.45, 0.20, 0.35)$, the last two
variants are valid and carry weight $0.55$, yet the mid-point percentiles of the first two are $0.225$ and
$0.55$, so $\hat\beta_{\mathrm{WM}} = -2/13$ for every $N$.

## Depends on

- [Weighted median Mendelian randomization estimator](weighted-median-mr-estimator.md)

## Expansion

Fix $\varepsilon > 0$ and put $m = \max_j w_j$. With probability tending to $1$, every $j \in V$ has
$|\hat\beta_j - \beta| < \varepsilon$ and $\sum_{j \in V} w_j - m/2 > 1/2$, since the limit of the left side
exceeds $1/2$. On this event, let $A$ (resp. $C$) be the variants with $\hat\beta_j \le \beta - \varepsilon$
(resp. $\ge \beta + \varepsilon$) and $W$ the rest, which contains $V$. In the ordering, $A$ comes first, then
$W$, then $C$, and $A \cap V = C \cap V = \varnothing$, so the weights of $A$ and of $C$ are each below
$1/2 - m/2$. If $f$ and $l$ are the first and last positions of $W$, then
$p_f = w(A) + w_f/2 < 1/2$ and $p_l = 1 - w(C) - w_l/2 > 1/2$. Hence $1/2 \in (p_f, p_l)$, where $F_w$
interpolates only estimates of $W$, all in $(\beta - \varepsilon, \beta + \varepsilon)$, so
$|\hat\beta_{\mathrm{WM}} - \beta| < \varepsilon$.

## Sources

- J. Bowden, G. Davey Smith, P. C. Haycock, and S. Burgess, "Consistent Estimation in Mendelian Randomization with Some Invalid Instruments Using a Weighted Median Estimator", Genetic Epidemiology 40 (2016), 304–314, <https://doi.org/10.1002/gepi.21965> (PMC4849733). Web Appendix 1 (empirical versus mid-point interpolated median, a counterexample to majority-only consistency for the latter, and the guarantee under a 10% maximum weight with 55% valid weight); the general sufficient margin above is derived here.
