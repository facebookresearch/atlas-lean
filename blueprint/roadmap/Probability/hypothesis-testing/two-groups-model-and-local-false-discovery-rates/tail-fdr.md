# Tail-area false discovery rate

In a [two-groups model](two-groups-model.md) $(\pi_0, f_0, f_1)$ with [mixture density](mixture-density.md) $f$, the tail-area false discovery rate of a region $\Gamma \subseteq \mathbb{R}$ is

$$\operatorname{Fdr}(\Gamma) = \frac{\pi_0 \int_\Gamma f_0}{\int_\Gamma f},$$

with the integrals taken as Lebesgue integrals over $\Gamma$, for every $\Gamma \subseteq \mathbb{R}$. For measurable $\Gamma$ this is $\pi_0 P_0(\Gamma)/P(Z \in \Gamma)$ written with the densities. Efron's $\operatorname{Fdr}(z)$ is $\operatorname{Fdr}((-\infty, z])$. It is $0$ when $\int_\Gamma f = 0$.

## Sources

- B. Efron, "Microarrays, empirical Bayes and the two-groups model", *Statist. Sci.* 23 (2008) 1–22, arXiv:0808.0572. Equation (2.3), $\operatorname{Fdr}(z) = p_0 F_0(z)/F(z)$, the case $\Gamma = (-\infty, z]$; the text notes that $Z > z$ or $|Z| > z$ may be used instead.
