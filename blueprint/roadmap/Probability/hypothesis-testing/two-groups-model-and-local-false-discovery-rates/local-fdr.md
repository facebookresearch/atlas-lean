# Local false discovery rate

In a [two-groups model](two-groups-model.md) $(\pi_0, f_0, f_1)$ with [mixture density](mixture-density.md) $f$, Efron's local false discovery rate is

$$\operatorname{fdr}(z) = \frac{\pi_0 f_0(z)}{f(z)},$$

with $\operatorname{fdr}(z) = 0$ where $f(z) = 0$.

## Sources

- B. Efron, "Microarrays, empirical Bayes and the two-groups model", *Statist. Sci.* 23 (2008) 1–22, arXiv:0808.0572. Equations (2.6)–(2.7): $f = p_0 f_0 + p_1 f_1$ and $\operatorname{fdr}(z) = p_0 f_0(z)/f(z)$, with $p_0 = \pi_0$.
