# Pleiotropic scaling model of trait and fitness effects

Consider a diploid Wright–Fisher population of stationary effective size $N_e$ in which every new mutation is semidominant and deleterious, with genotype fitnesses $1$, $1 - s$, $1 - 2s$ and effects $0$, $z$, $2z$ on a quantitative trait that is not itself under direct selection. Let $S = 4N_e s$ have density $g$ on $(0, \infty)$, and relate the trait effect to the selection strength by

$$z = \delta\, S^{\tau} (1 + \epsilon),$$

where $\tau \ge 0$, $\epsilon \sim N(0, \sigma^2)$, and $\delta \in \{-1, +1\}$ with equal probabilities, all independent of $S$ ($\delta = +1$ if the trait is fitness itself). Then $\mathbb{E}[z^2 \mid S] = (1 + \sigma^2) S^{2\tau}$. Assume free recombination, additivity across loci, and mutation–selection–drift balance, and let $H(S, x)$ be the expected time a new mutation of strength $S$ spends at frequency $x$. The additive variance in the trait contributed by mutations at frequency $x \in (0, 1)$ is then proportional to

$$V(x) \propto (1 + \sigma^2) \int_0^\infty g(S)\, H(S, x)\, 2x(1-x)\, S^{2\tau}\, dS,$$

and the total variance $V_T = \int_0^1 V(x)\, dx$ carries the same factor $1 + \sigma^2$. Consequently:

1. The distribution of trait variance over allele frequency, $V(x)/V_T$, does not depend on $\sigma$: however weak the correlation between trait and fitness effects, it is the same as when the trait is fitness ($\tau = 1$, $\sigma = 0$) whenever $\tau = 1$.
2. For $\tau = 0$ the trait effects are independent of selection, and the frequency distribution of trait variance is that of the neutral and nearly neutral mutations, which segregate at high frequency.
3. For $\tau = 1$, when the mean of $S$ is large most trait variance is contributed by rare, strongly selected mutations, which is invisible to association studies of common variants.

## Remarks

A mutation of trait effect $z$ at frequency $x$ contributes $2x(1-x)z^2$ to the additive variance. Integrating over the sojourn density of new mutations, over $g$, and over the conditional law of $z$ given $S$ replaces $z^2$ by $\mathbb{E}[z^2 \mid S] = S^{2\tau}\mathbb{E}[(1+\epsilon)^2] = (1+\sigma^2) S^{2\tau}$, since $\delta^2 = 1$. The factor $1 + \sigma^2$ cancels in $V(x)/V_T$. The weight $S^{2\tau}$ tilts the variance towards strongly selected mutations, which selection holds at low frequency; at $\tau = 0$ the weight is flat. With a gamma distribution for $g$ the integrals have closed forms involving the Hurwitz zeta function. A unimodal alternative, in which the trait effect has standard deviation proportional to $S^\tau$ without the factor $1 + \epsilon$, gives the same conclusions without the factor $1 + \sigma^2$.

## Depends on

- [Sojourn density of the Wright–Fisher diffusion with selection](../../../../../population-genetics/diffusion-theory/allele-age-and-the-maruyama-effect/selection-green.md)

## Sources

- A. Eyre-Walker, Genetic architecture of a complex trait and its implications for fitness and genome-wide association studies, *Proc. Natl. Acad. Sci. USA* 107 (2010), 1752–1756, <https://doi.org/10.1073/pnas.0906182107>, PMCID PMC2868283 (Model, Eqs. 1, 3, 6 and 7; Results; Discussion).
