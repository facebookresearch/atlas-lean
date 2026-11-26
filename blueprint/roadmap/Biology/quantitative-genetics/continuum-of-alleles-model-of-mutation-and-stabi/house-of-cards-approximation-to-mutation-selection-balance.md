# House-of-cards approximation for polygenic mutation–selection balance

Let a quantitative character be determined additively by $n$ diploid loci, each mutating at rate $\mu$ per gamete per generation. A mutation replaces the allelic effect with a new value drawn independently of the old one (house-of-cards mutation), with typical squared effect $a^2$. Stabilizing selection on the phenotype is Gaussian, $w(z) = \exp(-(z-\theta)^2/(2\omega^2))$, and the effective strength of selection on genotypic values is $V_s = \omega^2 + V_E$. In the **house-of-cards regime**, where mutations are rare and of large effect relative to the standing variance per locus ($\mu \ll a^2/V_s$), the equilibrium additive genetic variance is approximately

$$V_G \approx 4\, n\, \mu\, V_s = 2\, U\, V_s, \qquad U = 2n\mu,$$

independent of the distribution of mutational effects. This contrasts with the Gaussian (continuum-of-alleles) approximation, in which mutational effects are small relative to the standing variation and $V_G$ scales like $\sqrt{\mu\, a^2\, V_s}$ per locus, as in [Lande's equilibrium](lande-equilibrium-variance-with-linked-loci.md). The two approximations bracket the equilibrium variance across the plausible parameter range.

## Depends on

- [Gaussian stabilizing fitness](fitness.md)
- [Lande's equilibrium genetic variance under mutation and stabilizing selection with linked loci](lande-equilibrium-variance-with-linked-loci.md)

## Proof depends on

- [Gaussian stabilizing fitness](fitness.md)
- [The frequency $U/s$ is an equilibrium](../../population-genetics/mutation-selection-balance/diploid-step-mult-fixed.md)

## Expansion

With the population mean at the optimum, a rare allele that shifts the genotypic value by $a$ lowers heterozygote fitness by $s \approx a^2/(2V_s)$. At mutation–selection balance such alleles have frequency about $\mu/s = 2\mu V_s/a^2$. A diploid locus with a rare variant of effect $a$ at frequency $p$ contributes about $2pa^2$ to the additive variance, which gives $2 \cdot (2\mu V_s/a^2) \cdot a^2 = 4\mu V_s$ per locus. The effect size cancels, so summing over $n$ loci gives $4n\mu V_s$.

## Sources

- M. Turelli, *Heritable genetic variation via mutation–selection balance: Lerch's zeta meets the abdominal bristle*, Theor. Popul. Biol. 25 (1984), 138–193, <https://doi.org/10.1016/0040-5809(84)90017-0> (house-of-cards approximation to the equilibrium genetic variance and its comparison with the Gaussian approximation). The heuristic derivation is given above.
