# Tail-area fdr is the average local fdr over the region

In a [two-groups model](two-groups-model.md), for every $\Gamma \subseteq \mathbb{R}$,

$$\operatorname{Fdr}(\Gamma) = \frac{\int_\Gamma \operatorname{fdr}(z) f(z)\, dz}{\int_\Gamma f(z)\, dz}:$$

the tail-area false discovery rate is the $f$-weighted average of the local false discovery rate over $\Gamma$ (Efron 2010, Chapter 5). For measurable $\Gamma$ with $P(Z \in \Gamma) > 0$ the right side is $\mathbb{E}[\operatorname{fdr}(Z) \mid Z \in \Gamma]$ written with densities. Both sides are $0$ when $\int_\Gamma f = 0$.

## Sources

- B. Efron, "Microarrays, empirical Bayes and the two-groups model", *Statist. Sci.* 23 (2008) 1–22, arXiv:0808.0572. Equation (2.8), $\operatorname{Fdr}(z) = E_f\{\operatorname{fdr}(Z) \mid Z \le z\}$, the case $\Gamma = (-\infty, z]$.
