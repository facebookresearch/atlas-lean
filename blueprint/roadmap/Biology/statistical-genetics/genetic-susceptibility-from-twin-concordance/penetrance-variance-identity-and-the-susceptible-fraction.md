# Penetrance variance identity and the susceptible fraction

Partition a population $Z$ into $n$ equally frequent genotypes and let the susceptible subset $G$ consist of the $m$ genotypes $G_i$ with penetrance $x_i = \mathbb P(D \mid G_i) > 0$ for a disease $D$ (lifetime risk). Write $x = \mathbb P(D \mid G) = \frac1m\sum_i x_i$ for the mean penetrance, $\sigma_X^2 = \frac1m\sum_i (x_i - x)^2$ for its variance, $P(G) = m/n$ for the susceptible fraction, and $x' = \mathbb P(D \mid G, \mathrm{IG}_D)$ for the risk of an individual whose monozygotic co-twin has $D$ (and who is therefore in $G$). Assume monozygotic twinning is non-hereditary, so a twin's unconditional risk equals $\mathbb P(D)$, and that, given the genotype, a twin's risk does not depend on the co-twin's status.

**Susceptible fraction.** Since $D \subseteq G$,
$$P(G) = \frac{\mathbb P(D)}{\mathbb P(D \mid G)} = \frac{\mathbb P(D)}{x}.$$

**Variance identity.** The co-twin recurrence risk satisfies
$$x' = \frac{\mathbb E[x_i^2]}{x} = x + \frac{\sigma_X^2}{x}, \qquad\text{equivalently}\qquad \sigma_X^2 = x\,(x' - x).$$

**Solutions.** Hence $x$ solves $x^2 - x'x + \sigma_X^2 = 0$, i.e. $x = \tfrac12\big(x' \pm \sqrt{x'^2 - 4\sigma_X^2}\big)$, which is real only if $\sigma_X^2 \le (x'/2)^2$, the maximal variance of a distribution on $[0, x']$. The mean penetrance therefore lies either in the upper range $x'/2 < x \le x'$ (low variance; $x = x'$ iff all susceptible genotypes have equal penetrance) or in the lower range $0 < x < x'/2$, and $x \le x'$ always, so $P(G) \ge \mathbb P(D)/x'$.

## Expansion

Conditional on the co-twin being affected, the shared genotype is drawn size-biased by penetrance: $\mathbb P(G_i \mid G, \mathrm{IG}_D) = x_i/(mx)$. The twin is then affected with probability $x_i$, so $x' = \sum_i x_i^2/(mx) = \mathbb E[x_i^2]/x$, which is the variance identity. Because the variance on $[0, x']$ is maximized by a two-point distribution at $0$ and $x'$, which is excluded since every genotype in $G$ has positive penetrance, the two branches of the quadratic are separated at $x = x'/2$. Plugging observed prevalence and adjusted monozygotic recurrence risks into $P(G) = \mathbb P(D)/x$ gives explicit bounds; for multiple sclerosis in Europe and North America these imply that only a small minority of the population (under about 7.3%) is genetically susceptible, so environmental exposure alone cannot cause the disease in most people.

## Sources

- D. S. Goodin, P. Khankhanian, P.-A. Gourraud, N. Vince, "The nature of genetic and environmental susceptibility to multiple sclerosis", PLoS ONE 16(3) (2021) e0246157, Methods, Tables 1–2 and the derivation of the Upper and Lower Solutions, <https://doi.org/10.1371/journal.pone.0246157>, PMCID PMC7984655.
