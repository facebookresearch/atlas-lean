# Proportional rescaling to the all-cause envelope

Fix a stratum (location, year, age group and sex) and a set of mutually exclusive, collectively exhaustive causes $c = 1,\dots,J$. Let $d_c^{(s)} \ge 0$ be the $s$-th posterior draw of deaths from cause $c$ produced by cause-specific models, with $\sum_c d_c^{(s)} > 0$, and let $E^{(s)} \ge 0$ be the $s$-th draw of all-cause deaths (the **envelope**). The proportionally corrected draws are

$$\tilde d_c^{(s)} = d_c^{(s)}\, \frac{E^{(s)}}{\sum_{c'=1}^{J} d_{c'}^{(s)}} .$$

**Proposition.**

1. $\sum_c \tilde d_c^{(s)} = E^{(s)}$ for every draw $s$.
2. Cause fractions are preserved: when $E^{(s)} > 0$, $\tilde d_c^{(s)} / E^{(s)} = d_c^{(s)} / \sum_{c'} d_{c'}^{(s)}$ (when $E^{(s)} = 0$ every corrected draw is $0$ and the corrected cause fractions are undefined), and $\tilde d_c^{(s)}/\tilde d_{c'}^{(s)} = d_c^{(s)}/d_{c'}^{(s)}$ whenever $E^{(s)} > 0$ and $d_{c'}^{(s)} > 0$.
3. $\tilde d^{(s)}$ is the unique vector proportional to $d^{(s)}$ that sums to $E^{(s)}$.

## Remarks

All three statements follow because the correction multiplies every cause in a draw by the same factor $E^{(s)}/\sum_{c'} d_{c'}^{(s)}$. Pairing draws of cause-specific models with draws of the all-cause model (1,000 each in the source) propagates the uncertainty of both into the corrected estimates; summaries (means and 95% uncertainty intervals) are taken across corrected draws. The correction assumes that the cause-specific models are right about relative magnitudes and the envelope about the total. Where some causes are known to be systematically misattributed, the uniform factor is replaced by a rule that moves deaths preferentially between specific causes; the source does this for Alzheimer's and Parkinson's disease deaths miscoded to causes such as lower respiratory infections and cerebrovascular disease.

## Sources

- GBD 2016 Causes of Death Collaborators, "Global, regional, and national age-sex specific mortality for 264 causes of death, 1980–2016: a systematic analysis for the Global Burden of Disease Study 2016", The Lancet 390 (2017) 1151–1210, Methods ("CoDCorrect algorithm for combining estimates"), <https://doi.org/10.1016/S0140-6736(17)32152-9>, PMCID PMC5605883.
