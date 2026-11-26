# Penetrance variance identity and the susceptible fraction

Partition a population $Z$ into $n$ equally frequent genotypes and let the susceptible subset $G$ consist of the $m$ genotypes $G_i$ with penetrance $x_i = \mathbb P(D \mid G_i) > 0$ for a disease $D$ (lifetime risk). Write $x = \mathbb P(D \mid G) = \frac1m\sum_i x_i$ for the mean penetrance, $\sigma_X^2 = \frac1m\sum_i (x_i - x)^2$ for its variance, $P(G) = m/n$ for the susceptible fraction, and $x' = \mathbb P(D \mid G, \mathrm{IG}_D)$ for the risk of an individual whose monozygotic co-twin has $D$ (and who is therefore in $G$). Assume monozygotic twinning is non-hereditary, so a twin's unconditional risk equals $\mathbb P(D)$, and that, given the genotype, a twin's risk does not depend on the co-twin's status.

**Susceptible fraction.** Since $D \subseteq G$,

$$P(G) = \frac{\mathbb P(D)}{\mathbb P(D \mid G)} = \frac{\mathbb P(D)}{x}.$$

**Variance identity.** The co-twin recurrence risk satisfies

$$x' = \frac{\mathbb E[x_i^2]}{x} = x + \frac{\sigma_X^2}{x}, \qquad\text{equivalently}\qquad \sigma_X^2 = x\,(x' - x).$$

**Solutions.** Hence $x$ solves $x^2 - x'x + \sigma_X^2 = 0$, i.e. $x = \tfrac12\big(x' \pm \sqrt{x'^2 - 4\sigma_X^2}\big)$, and since $x$ is a real root, $\sigma_X^2 \le (x'/2)^2$. The mean penetrance therefore lies either in the upper range $x'/2 \le x \le x'$ (the $+$ root; $x = x'$ iff all susceptible genotypes have equal penetrance) or in the lower range $0 < x \le x'/2$ (the $-$ root). The two ranges meet at $x = x'/2$, which is attained, for example by three susceptible genotypes with penetrances $t$, $t$ and $(4 + 3\sqrt2)\,t$ for small $t > 0$. Since $x' - x = \sigma_X^2/x \ge 0$, always $x \le x'$, so $P(G) \ge \mathbb P(D)/x'$.

## Depends on

Its statement uses only the notions recalled above.

## Proof depends on

Its proof consists of the steps listed under Expansion.

## Expansion

Conditional on the co-twin being affected, the shared genotype is drawn size-biased by penetrance: $\mathbb P(G_i \mid G, \mathrm{IG}_D) = x_i/(mx)$. The twin is then affected with probability $x_i$, so $x' = \sum_i x_i^2/(mx) = \mathbb E[x_i^2]/x$, which is the variance identity. The two branches of the quadratic meet where its discriminant vanishes, $\sigma_X^2 = x'^2/4$, that is at $x = x'/2$. Individual penetrances are not bounded by $x'$: in the example above $x = (2 + \sqrt2)\,t$, $x' = (4 + 2\sqrt2)\,t$, and the largest penetrance $(4 + 3\sqrt2)\,t$ exceeds $x'$. Plugging observed prevalence and adjusted monozygotic recurrence risks into $P(G) = \mathbb P(D)/x$ gives explicit bounds; for multiple sclerosis in Europe and North America these imply that only a small minority of the population (under about 7.3%) is genetically susceptible, so environmental exposure alone cannot cause the disease in most people.

## Sources

- D. S. Goodin, P. Khankhanian, P.-A. Gourraud, N. Vince, "The nature of genetic and environmental susceptibility to multiple sclerosis", PLoS ONE 16(3) (2021) e0246157, Methods, Tables 1–2 and the derivation of the Upper and Lower Solutions, <https://doi.org/10.1371/journal.pone.0246157>, PMCID PMC7984655.
