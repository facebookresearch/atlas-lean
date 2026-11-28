# Exponentially scaled odds of pathogenicity

**Setting.** A sequence variant has prior probability of pathogenicity $P_0 \in (0,1)$. Each evidence item is treated as an odds of pathogenicity (a likelihood ratio, $>1$ for pathogenic and $<1$ for benign evidence), and the items are assumed conditionally independent, so their odds multiply (a naive Bayes classifier). The four pathogenic strength levels, supporting (Su), moderate (M), strong (St) and very strong (VSt), are scaled exponentially with a common exponent $X > 1$:

$$O_{\mathrm{Su}}^{X} = O_{\mathrm M},\qquad O_{\mathrm M}^{X} = O_{\mathrm{St}},\qquad O_{\mathrm{St}}^{X} = O_{\mathrm{VSt}},$$

and each benign level has the reciprocal odds of the pathogenic level of the same strength.

**Combined odds.** If a classification uses $N_{\mathrm{Su}}, N_{\mathrm M}, N_{\mathrm{St}}, N_{\mathrm{VSt}}$ pathogenic items and $N_{\mathrm{BSu}}, N_{\mathrm{BSt}}$ benign supporting and strong items, the combined odds of pathogenicity are

$$O_P = O_{\mathrm{VSt}}^{\,N_{\mathrm{Su}}/X^3 + N_{\mathrm M}/X^2 + N_{\mathrm{St}}/X + N_{\mathrm{VSt}} \;-\; N_{\mathrm{BSu}}/X^3 - N_{\mathrm{BSt}}/X}.$$

**Posterior.** By Bayes' rule in odds form,

$$\mathrm{Post}_P = \frac{O_P\,P_0}{(O_P - 1)P_0 + 1}.$$

Classification uses posterior thresholds: pathogenic if $\mathrm{Post}_P > 0.99$, likely pathogenic if $0.90 < \mathrm{Post}_P \le 0.99$, likely benign if $0.001 \le \mathrm{Post}_P < 0.10$, benign if $\mathrm{Post}_P < 0.001$, and uncertain significance otherwise.

With the calibration $X = 2$, $O_{\mathrm{VSt}} = 350$ the four pathogenic levels have odds $350^{1/8} \approx 2.08$, $350^{1/4} \approx 4.33$, $350^{1/2} \approx 18.7$ and $350$.

## Depends on

- [Formula for the positive predictive value](../../../epidemiology/sensitivity-specificity-and-predictive-values/ppv-eq.md)

## Expansion

Posterior odds equal the likelihood ratio times the prior odds, $\mathrm{Post}_P/(1-\mathrm{Post}_P) = O_P\,P_0/(1-P_0)$; solving for $\mathrm{Post}_P$ gives the displayed formula. Conditional independence makes the log odds additive, so one evidence item of level $\ell$ contributes $X^{-m(\ell)}\ln O_{\mathrm{VSt}}$ with $m = 3, 2, 1, 0$ for Su, M, St, VSt, and benign items subtract the same amounts; mixed pathogenic and benign evidence is therefore combined by adding exponents. The exponential scaling means two items of one level weigh as much as one item of the next level up exactly when $X = 2$. The independence assumption is the main modelling caveat: correlated lines of evidence (for example two computational predictors) would be double-counted.

## Sources

- S. V. Tavtigian, M. S. Greenblatt, S. M. Harrison et al., "Modeling the ACMG/AMP variant classification guidelines as a Bayesian classification framework", Genetics in Medicine (2018), Methods, Equations (1)–(2), and Results, Equations (3)–(4), <https://doi.org/10.1038/gim.2017.210> (PMC6336098).
- S. Richards et al., "Standards and guidelines for the interpretation of sequence variants: a joint consensus recommendation of the American College of Medical Genetics and Genomics and the Association for Molecular Pathology", Genetics in Medicine (2015), <https://doi.org/10.1038/gim.2015.30>.
