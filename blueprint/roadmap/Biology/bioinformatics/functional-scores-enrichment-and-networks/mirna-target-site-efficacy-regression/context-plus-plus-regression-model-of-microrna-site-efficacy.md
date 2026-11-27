# Context++ regression model of microRNA site efficacy

Fix a canonical site type $\tau \in \{\text{8mer}, \text{7mer-m8}, \text{7mer-A1}, \text{6mer}\}$
(a match to the microRNA seed region within a 3' UTR). For a site $u$ of type $\tau$ let
$x_1(u), \dots, x_p(u)$ be its features (for example local AU content, minimum distance to a
3'-UTR end, 3'-supplementary pairing, predicted seed-pairing stability, target-site abundance,
3'-UTR and ORF lengths, predicted structural accessibility, numbers of offset-6mer and ORF 8mer
sites, site conservation and identities of key nucleotides). Features with skewed distributions
enter on the $\log_{10}$ scale: the 3'-UTR and ORF lengths, the minimum distance to a 3'-UTR end and
the predicted structural accessibility are replaced by their base-10 logarithms (Table 1) before
scaling. Each continuous feature, so transformed, is then mapped to a comparable scale by trimmed
min-max normalization,

$$\tilde x_\ell(u) \;=\; \frac{x_\ell(u) - q^{(\tau)}_{\ell,0.05}}{q^{(\tau)}_{\ell,0.95} - q^{(\tau)}_{\ell,0.05}},$$

with $q^{(\tau)}_{\ell,\alpha}$ the $\alpha$-quantile of feature $\ell$ over sites of type $\tau$.
The **context++ score** of the site is the fitted value of a site-type-specific multiple linear
regression of the $\log_2$ fold change of single-site mRNAs after microRNA introduction, bounded
above by a site-type cap,

$$s(u) \;=\; \min\Bigl(\beta^{(\tau)}_0 + \sum_{\ell=1}^{p} \beta^{(\tau)}_\ell\, \tilde x_\ell(u),\ c_\tau\Bigr),$$

with $c_\tau = -0.03, -0.02, -0.01, 0$ for $\tau = $ 8mer, 7mer-m8, 7mer-A1, 6mer respectively, so
$s$ is a piecewise linear function of the scaled features and never positive; more negative scores
predict stronger repression. For an mRNA with several sites $u_1, \dots, u_q$ to the same
microRNA, the predicted total effect is the sum of the capped site scores
$S = \sum_{h=1}^{q} s(u_h)$, which
treats sites as acting independently and multiplicatively on expression (additively on the
$\log_2$ scale).

## Remarks

The features were chosen by AIC-guided stepwise regression (from 26 candidates) on 1000 random 70%
training splits of mRNAs with a single site, retaining the 14 features selected in nearly all splits
for at least two site types; the final coefficients were refitted on all data, one model per site
type, and evaluated by $r^2$ on held-out 30% splits. The trimmed normalization prevents outliers from
dominating and makes coefficient magnitudes roughly comparable as measures of feature importance;
the intercept per site type captures the baseline discriminatory power of the site type. The sign
of a coefficient gives the direction of the effect: longer ORFs and 3' UTRs reduce repression
(positive coefficients), while accessible sites and additional ORF 8mer sites increase it
(negative coefficients).

## Sources

- V. Agarwal, G. W. Bell, J.-W. Nam, D. P. Bartel, "Predicting effective microRNA target sites in mammalian mRNAs", *eLife* 4 (2015) e05005, <https://doi.org/10.7554/eLife.05005> (PMC4532895), Results, "Selecting features and building a regression model for target prediction" (Table 1, Figure 4), the summing of context++ scores for 3' UTRs with multiple sites, and Materials and methods, "Stepwise regression and multiple linear regression models" (site-type caps) and "Scaling the scores of each feature" ($\log_{10}$ transforms, trimmed normalization, Table 3).
