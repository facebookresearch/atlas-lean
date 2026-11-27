# Colony dynamics model for worker-sterility alleles

**Setting.** A large haplodiploid population (diploid females, haploid males) has two alleles at one locus: $A$ (workers lay male eggs) and $a$ (workers do not). Every virgin queen (gyne) mates with $n \ge 1$ males drawn at random from the population. A colony is labelled by its queen's genotype $G \in \{AA, Aa, aa\}$ and the number $m \in \{0, \dots, n\}$ of her mates carrying $a$; $X_{G,m}$ is the number of such colonies. Let $x_{AA}, x_{Aa}, x_{aa}$ be the numbers of gynes and $y_A, y_a$ the numbers of drones produced. The colony numbers evolve by

$$\dot X_{G,m} = \binom{n}{m}\, x_G\, y_A^{\,n-m} y_a^{\,m} - \phi\, X_{G,m}, \qquad \phi = \frac{(x_{AA} + x_{Aa} + x_{aa})(y_A + y_a)^n}{c},$$

where the density-dependent death rate $\phi$ keeps the total number of colonies $\sum_{G,m} X_{G,m} = c$ constant.

**Colony phenotype.** If a fraction $z$ of a colony's workers is non-reproductive, the colony produces reproductives at rate $r_z$, and a fraction $p_z$ of its males are laid by the queen (the rest by reproductive workers, in proportion to their genotypes); $p_1 = 1$, and one normalizes $r_0 = 1$. Females are produced by the queen from her two alleles and her mates' sperm, males by the queen (one of her alleles) or by workers (one of a worker's alleles).

**Recessive sterility ($aa$ workers sterile).** The sterile worker fraction is $z = 0$ in $AA,m$ colonies, $z = m/(2n)$ in $Aa,m$ colonies and $z = m/n$ in $aa,m$ colonies. Up to the common factors for the fraction of offspring that become reproductives (which drop out of all conditions), the gyne numbers are

$$x_{AA} = \sum_m \Big[\tfrac{n-m}{n} r_0 X_{AA,m} + \tfrac{n-m}{2n} r_{m/2n} X_{Aa,m}\Big],$$

$$x_{Aa} = \sum_m \Big[\tfrac{m}{n} r_0 X_{AA,m} + \tfrac12 r_{m/2n} X_{Aa,m} + \tfrac{n-m}{n} r_{m/n} X_{aa,m}\Big], \qquad x_{aa} = \sum_m \Big[\tfrac{m}{2n} r_{m/2n} X_{Aa,m} + \tfrac{m}{n} r_{m/n} X_{aa,m}\Big],$$

and the fraction of $A$ drones is $\frac{2n - m + m p_0}{2n}$ in $AA,m$ colonies, $\frac{n(3 - p) - m(2 - p)}{2(2n - m)}$ with $p = p_{m/2n}$ in $Aa,m$ colonies, and $\tfrac12 (1 - p_{m/n})$ in $aa,m$ colonies.

**Dominant sterility (any $a$ worker sterile).** Only $AA$ workers reproduce, so $z = m/n$ in $AA,m$ colonies, $z = (n+m)/(2n)$ in $Aa,m$ colonies and $z = 1$ in $aa,m$ colonies.

## Depends on

- [Mendel's law of segregation](../../hardy-weinberg-law/transmit.md)
- [Binomial law as a probability measure](../../../../Probability/central-limit-theorems/poisson-limit-theorem/binomial-prob-measure.md)

## Expansion

The binomial factor counts the orders in which a gyne of genotype $G$ can mate with $m$ mutant and $n - m$ wild-type drones, and summing the birth terms over $G$ and $m$ gives $(\sum_G x_G)(y_A + y_a)^n$, which is exactly cancelled by $\phi c$. The drone fractions follow by mixing the queen's output (fraction $p_z$) with the reproductive workers' output: e.g. in an $Aa,m$ colony the reproductive workers are the $AA$ fraction $(n-m)/(2n)$ and the $Aa$ fraction $1/2$, so among their sons a share $\frac{3n - 2m}{2(2n - m)}$ carries $A$, while the queen's sons are half $A$; combining with weights $p$ and $1 - p$ gives the formula above. Stochastic effects within colonies are neglected (each colony produces very many offspring), and worker sterility is assumed not to change the population sex ratio.

## Sources

- J. W. Olejarz, B. Allen, C. Veller and M. A. Nowak, "The evolution of non-reproductive workers in insect colonies with haplodiploid genetics", eLife 4 (2015), e08918, Model section and Materials and methods ("Description of the model", Eqs. (5)–(8), (14)–(15); Fig. 1), <https://doi.org/10.7554/eLife.08918>, PMCID PMC4755779.
