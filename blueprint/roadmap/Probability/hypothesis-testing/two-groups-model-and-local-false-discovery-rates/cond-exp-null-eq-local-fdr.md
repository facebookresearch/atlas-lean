# Local fdr is the posterior null probability

In a [two-groups model](two-groups-model.md), under the [joint law](joint-law.md) of $(H, Z)$, the conditional expectation of the null indicator given the z-value is the [local false discovery rate](local-fdr.md):

$$\mathbb{E}[\mathbf{1}\{H = 0\} \mid Z] = \operatorname{fdr}(Z) \quad \text{almost surely},$$

that is, $\operatorname{fdr}(Z) = P(H = 0 \mid Z)$ (Efron et al. 2001).

## Sources

- B. Efron, "Microarrays, empirical Bayes and the two-groups model", *Statist. Sci.* 23 (2008) 1–22, arXiv:0808.0572. Equation (2.7), $\operatorname{fdr}(z) \equiv \Pr\{\text{null} \mid Z = z\}$, obtained there by Bayes' rule.
