# Cornfield odds-ratio invariance under case-control sampling

Cornfield (1951) shows how rates are recovered from relative frequencies. Let $p_1$ and $p_2$ be the proportions with a characteristic (for example smoking) among persons with and without a disease, and $X$ the prevalence of the disease. The proportion with the characteristic in the population is $p_1 X + p_2(1 - X)$, the disease rate among those with the characteristic is $p_1 X/[p_2 + X(p_1 - p_2)]$ and among those without it $(1 - p_1) X/[(1 - p_2) - X(p_1 - p_2)]$ (formulas (1) and (2) of the source); the ratio of the two rates is therefore

$$\frac{p_1\,[(1 - p_2) - X(p_1 - p_2)]}{(1 - p_1)\,[p_2 + X(p_1 - p_2)]} \;\longrightarrow\; \frac{p_1 (1 - p_2)}{p_2 (1 - p_1)} \quad (X \to 0),$$

the odds ratio of the characteristic between diseased and control groups, which is Cornfield's approximation for a rare disease. This rests on an exact invariance. Let $E$ be a binary exposure and $D$ a binary disease with risks $r_1 = P(D \mid E)$ and $r_0 = P(D \mid \bar E)$ in $(0, 1)$, and let cases and controls be selected with probabilities $s_1, s_0 > 0$ that depend only on disease status. By Bayes' rule the selection probabilities cancel from the cross-product ratio, so the exposure odds ratio among the selected equals the population disease odds ratio $\mathrm{OR} = r_1(1 - r_0)/(r_0(1 - r_1))$ (Breslow and Day 1980, Ch. 2); in a logistic model, [case-control sampling shifts only the logistic intercept](../../../not-yet-classified/case-control-logistic.md). Moreover $\mathrm{OR}/\mathrm{RR} = (1 - r_0)/(1 - r_1)$ with $\mathrm{RR} = r_1/r_0$ (equivalently $\mathrm{RR} = \mathrm{OR}/(1 - r_0 + r_0\,\mathrm{OR})$, Zhang and Yu 1998), so $\mathrm{OR}/\mathrm{RR} \to 1$ as $r_0, r_1 \to 0$ (the rare disease assumption), and $\mathrm{OR} > \mathrm{RR} > 1$ if $r_1 > r_0$, while $\mathrm{OR} < \mathrm{RR} < 1$ if $r_1 < r_0$.

## Expansion

1. The model: a joint law of $(E, D)$ and a selection indicator whose conditional law given $(D, E)$ depends on $D$ only.
2. Cornfield's formulas (1) and (2) for the rates from the relative frequencies and the prevalence, and the approximation when the prevalence is small.
3. Bayes' rule for $P(E \mid D, S)$, cancellation of the selection probabilities, and the symmetry of the odds ratio between the exposure and disease margins.
4. The identity $\mathrm{OR}/\mathrm{RR} = (1 - r_0)/(1 - r_1)$, the rare-disease limit, and the ordering statement.
5. The relative risk is not identified from case-control data without the rare-disease limit or external prevalence information, as a separate statement.

## Sources

- J. Cornfield, A method of estimating comparative rates from clinical data; applications to cancer of the lung, breast, and cervix, J. Natl. Cancer Inst. 11 (1951), 1269–1275, formulas (1) and (2). <https://doi.org/10.1093/jnci/11.6.1269>
- N. E. Breslow and N. E. Day, *Statistical Methods in Cancer Research, Vol. I: The Analysis of Case-Control Studies*, IARC Scientific Publications 32, International Agency for Research on Cancer, Lyon, 1980, Ch. 2.
- J. Zhang and K. F. Yu, What's the relative risk? A method of correcting the odds ratio in cohort studies of common outcomes, JAMA 280 (1998), 1690–1691. <https://doi.org/10.1001/jama.280.19.1690>
