# Invasion condition for a homing gene drive

Consider an infinite, randomly mating diploid population at one locus with a wild-type allele $W$ and a drive allele $D$ (other alleles absent). Genotype $AB$ has viability $f_{AB} > 0$, and an individual of genotype $AB$ produces a gamete carrying allele $C$ with probability $p_{AB,C}$; segregation is Mendelian ($p_{AB,A} = p_{AB,B} = \tfrac12$ for $A \ne B$) except in drive heterozygotes, where homing biases transmission so that $p_{WD,D} \in [\tfrac12, 1]$ (with $p_{WD,W} \le 1 - p_{WD,D}$, the remainder going to resistant alleles). Genotype frequencies evolve by random union of gametes produced in proportion to viability-weighted transmission, with a density-dependent death rate keeping the total at $1$ (Noble et al., continuous-time model).

**Theorem (invasion).** The drive-free equilibrium (all individuals $WW$) is unstable to introduction of a rare drive allele, so the drive invades, if

$$2\, p_{WD,D}\, f_{WD} > f_{WW},$$

and the drive allele declines when rare if $2\, p_{WD,D}\, f_{WD} < f_{WW}$.

The condition is independent of the molecular mechanism behind $p_{WD,D}$ and of the fitness and production of resistant alleles, which are absent at first order when the drive is rare.

## Expansion

In the model, the gamete-production rates are $F_C = \sum_{AB} p_{AB,C} f_{AB} x_{AB}$, heterozygote frequencies obey $\dot x_{WD} = 2 F_W F_D - \psi^2 x_{WD}$ (the factor $2$ counts both orders of gamete union), homozygotes obey $\dot x_{DD} = F_D^2 - \psi^2 x_{DD}$, and $\psi = \sum_C F_C$ keeps the total frequency at $1$. Near the drive-free state, $x_{WD} = O(\varepsilon)$, $x_{DD} = O(\varepsilon^2)$, $F_W = f_{WW} + O(\varepsilon)$, $\psi = f_{WW} + O(\varepsilon)$ and $F_D = p_{WD,D} f_{WD} x_{WD}$. Hence to first order

$$\dot x_{WD} = \big(2\, p_{WD,D} f_{WD} - f_{WW}\big) f_{WW}\, x_{WD},$$

and resistant alleles produced by $WD$ individuals enter only at order $\varepsilon$ in their own heterozygotes with $D$, not in this growth rate. The sign of $2 p_{WD,D} f_{WD} - f_{WW}$ decides invasion. With Mendelian transmission $p_{WD,D} = \tfrac12$ the condition becomes the classical criterion $f_{WD} > f_{WW}$ for a rare allele under Mendelian inheritance. Published CRISPR constructs with $p_{WD,D} \approx 0.95$ invade as long as the heterozygote's fitness exceeds about $0.53\, f_{WW}$, matching their rapid spread in laboratory populations.

## Sources

- C. Noble, J. Olejarz, K. M. Esvelt, G. M. Church and M. A. Nowak, "Evolutionary dynamics of CRISPR gene drives", Science Advances 3 (2017), e1601964, Results Eq. (1) and Materials and Methods (model equations; derivation in Supplementary sections S3 and S7.1), <https://doi.org/10.1126/sciadv.1601964>, PMCID PMC5381957.
