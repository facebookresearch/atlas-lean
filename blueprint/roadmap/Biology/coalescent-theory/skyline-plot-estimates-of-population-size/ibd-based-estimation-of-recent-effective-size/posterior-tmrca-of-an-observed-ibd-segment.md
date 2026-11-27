# Posterior TMRCA of an observed IBD segment

Let $N = (N[g])_{g \ge 0}$ be diploid effective sizes (so $2N[g]$ haplotypes) $g$ generations before the present, with $N[g] = N[G]$ for $g > G$, and suppose close relatives have been removed so that segments come from TMRCA $g \ge g^\ast$ (and $1 - 1/(2N[g]) \approx 1$ for $g < g^\ast$). Under the Wright–Fisher model

$$P(\mathrm{TMRCA} = g \mid N) = \frac{1}{2N[g]} \prod_{g'=g^\ast}^{g-1}\Bigl(1 - \frac{1}{2N[g']}\Bigr). \tag{A1}$$

Assume Haldane crossovers at rate $1/100$ per cM per meiosis on a chromosome of length $L$ cM. Given TMRCA $g$ there are $2g$ meioses, so from any covered position $h$ each end of the segment lies at an exponential distance with rate $g/50$ per cM. For an observed segment $[s_1, s_2]$ of length $l = s_2 - s_1$ covering $h$:

- interior ($0 < s_1 < s_2 < L$): $P(\mathrm{TMRCA} = g \mid l, N) = \gamma_0(l, N)^{-1} (g/50)^2 e^{-lg/50}\, P(\mathrm{TMRCA} = g \mid N)$;
- one end censored ($s_1 = 0$ or $s_2 = L$): the same with $(g/50)^2$ replaced by $g/50$ and normalizer $\gamma_1$;
- both ends censored ($l = L$): the same with the factor replaced by $1$ and normalizer $\gamma_2$.

None depends on $h$. With $\alpha = l/50$, $\beta = 1 - 1/(2N[G])$ and $\Pi_G = \prod_{g'=g^\ast}^{G}(1 - 1/(2N[g']))$, the tails of the normalizers beyond $G$ have closed forms, for instance

$$\gamma_0(l, N) = \sum_{g=g^\ast}^{G} \Bigl(\frac{g}{50}\Bigr)^{2} e^{-lg/50} P(\mathrm{TMRCA} = g \mid N) + \Pi_G\,\frac{(1-\beta)e^{-\alpha(G+1)}}{2500}\Bigl(\frac{G^2}{1-\beta e^{-\alpha}} + \frac{2G-1}{(1-\beta e^{-\alpha})^2} + \frac{2}{(1-\beta e^{-\alpha})^3}\Bigr),$$

$$\gamma_1(l, N) = \sum_{g=g^\ast}^{G} \frac{g}{50} e^{-lg/50} P(\mathrm{TMRCA} = g \mid N) + \Pi_G\,\frac{(1-\beta)e^{-\alpha(G+1)}}{50}\Bigl(\frac{G}{1-\beta e^{-\alpha}} + \frac{1}{(1-\beta e^{-\alpha})^2}\Bigr),$$

and $\gamma_2$ has tail $\Pi_G (1-\beta)e^{-\alpha(G+1)}/(1-\beta e^{-\alpha})$.

## Proof sketch

Equation (A1) is the geometric-type waiting time for two lineages, each generation choosing a common parental haplotype with probability $1/(2N[g])$. By Bayes' rule the posterior is the prior times the likelihood of the endpoints. For an interior segment the two endpoint densities multiply to $(g/50)^2 e^{-(h - s_1)g/50} e^{-(s_2 - h)g/50} = (g/50)^2 e^{-lg/50}$. A censored end contributes the survival probability $e^{-hg/50}$ rather than a density, which removes one factor $g/50$. Beyond $G$ the prior is $(1-\beta)\beta^{g-G-1}\Pi_G$, and the series $\sum_j r^j = 1/(1-r)$, $\sum_j (j+1) r^j = 1/(1-r)^2$, $\sum_j (j+1)(j+2) r^j = 2/(1-r)^3$ with $r = \beta e^{-\alpha} < 1$, after writing $(j + G + 1)^2 = G^2 + (2G - 1)(j+1) + (j+1)(j+2)$, give the closed-form tails. Because the posterior depends only on $l$ and the number of censored ends, it can be computed once per length bin.

## Proof depends on

- [Probability of no coalescence in one Wright–Fisher generation](../../kingman-s-coalescent-and-watterson-s-estimator/no-coal-prob.md)

## Sources

- S. R. Browning and B. L. Browning, "Accurate non-parametric estimation of recent effective population size from segments of identity by descent", American Journal of Human Genetics 97 (2015), 404–418, Appendix A ("Estimated Amount of Inferred IBD from Generation g", Equations A1–A2), <https://doi.org/10.1016/j.ajhg.2015.07.012>, PMCID PMC4564943.
