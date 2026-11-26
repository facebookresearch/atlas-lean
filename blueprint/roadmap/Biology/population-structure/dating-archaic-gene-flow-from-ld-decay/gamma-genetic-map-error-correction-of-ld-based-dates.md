# Gamma genetic-map error correction of LD-based dates

Let a genetic map assign distances $g_1, \dots, g_{m-1}$ to consecutive marker intervals, and model the true distances as independent

$$Z_i \sim \Gamma(\text{shape } \alpha g_i,\ \text{rate } \alpha), \qquad \mathbb E Z_i = g_i,\quad \operatorname{Var} Z_i = g_i/\alpha,$$

where the map-specific precision $\alpha > 0$ is larger for more accurate maps. The family is closed under merging intervals, $Z_1 + Z_2 \sim \Gamma(\alpha(g_1+g_2), \alpha)$, so $\alpha$ is a property of the map rather than of the marker spacing. If admixture LD decays as $e^{-tZ}$ in the true distance $Z$, then at observed distance $g$

$$\mathbb E\bigl[e^{-tZ}\bigr] = \Bigl(1 + \frac{t}{\alpha}\Bigr)^{-\alpha g} = e^{-\lambda g}, \qquad \lambda = \alpha\log\Bigl(1 + \frac{t}{\alpha}\Bigr),$$

so the curve is still exponential in $g$ but with a smaller rate. Inverting,

$$t = \alpha\bigl(e^{\lambda/\alpha} - 1\bigr) \ \ge\ \lambda,$$

with $t \to \lambda$ as $\alpha \to \infty$. Map error therefore biases the naive date $\hat t = \hat\lambda$ downward, and the corrected estimate needs $\alpha$, which is estimated by comparing the map with crossovers observed in a pedigree (posterior by Gibbs sampling). With $\hat\lambda \approx 1{,}200$ and the estimated map precisions, the corrected Neandertal gene-flow date in Europeans was about $1{,}800$–$2{,}000$ generations, or $47{,}000$–$65{,}000$ years with $25$–$33$ years per generation.

## Depends on

- [Exponential decay of LD among introgressed alleles](exponential-decay-of-ld-among-introgressed-alleles.md)

## Expansion

The Laplace transform of $\Gamma(k, \alpha)$ is $(1 + s/\alpha)^{-k}$; with $k = \alpha g$ and $s = t$ this equals $\exp(-g\,\alpha\log(1 + t/\alpha))$. Since $\log(1+u) < u$ for $u > 0$, $\lambda < t$: averaging an exponentially decaying signal over noisy distances flattens the decay, exactly as Jensen's inequality predicts for the convex function $z \mapsto e^{-tz}$. The bias grows with $t/\alpha$, which is why it matters for old events measured at the tens-of-kilobase scale, where maps are least accurate, and is negligible for recent admixture measured at the centimorgan scale.

## Sources

- S. Sankararaman, N. Patterson, H. Li, S. Pääbo, D. Reich, "The date of interbreeding between Neandertals and modern humans", PLoS Genetics 8 (2012) e1002947, Methods ("Correction for error in the genetic map", "Uncertainty in the date estimate"), Table 2 and Text S1 (Appendix B), <https://doi.org/10.1371/journal.pgen.1002947> (PMC3464203).
