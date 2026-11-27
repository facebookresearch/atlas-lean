# Invasion and stability of a queen-control allele

**Model.** In a large haplodiploid population every colony is headed by one queen who has mated with $n \ge 1$ males drawn at random. Workers cannot lay fertilized eggs but can lay haploid male eggs. A mutant allele $a$, expressed in queens (dominant or recessive), makes the queen suppress her workers' male production. In colonies headed by a wild-type queen a fraction $p \in [0, 1]$ of males is queen-produced and new gynes and drones are produced at rate $r > 0$; in colonies headed by a queen with the mutant phenotype the corresponding values are $p' \in [0, 1]$ and $r' > 0$. Colony types are tracked by the queen's genotype and the number $m \in \{0, \dots, n\}$ of mutant males she mated with.

**Statement** (Olejarz, Veller and Nowak 2017, Conditions (1) and (2)). Whether $a$ is dominant or recessive, and for every mating number $n$:

1. the queen-control allele invades a population of non-controlling queens if

$$\frac{r'}{r} > 1 - \frac{p' - p}{2 + p + p'};$$

2. once fixed, it resists invasion by the non-controlling allele if

$$\frac{r'}{r} > 1 - \frac{p' - p}{2(1 + p')}.$$

If $p' > p$, condition 1 is strictly weaker than condition 2, so three regimes occur: neither holds (control cannot invade), only condition 1 holds (control invades but cannot fix, and a mixed equilibrium exists), or both hold (control invades and is stable when fixed). For complete control, $p' = 1$, the stability condition reads $r'/r > (3 + p)/4$.

## Depends on

- [Colony dynamics model for worker-sterility alleles](../non-reproductive-workers-in-haplodiploid-colonies/colony-dynamics-model-for-worker-sterility-alleles.md)
- [Mendel's law of segregation](../../hardy-weinberg-law/transmit.md)

## Proof depends on

- [Lyapunov's indirect method (linearized stability), conditional decay form](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/global-solution-decay-of-has-fderiv-at.md)
- [Lyapunov's indirect method, instability](../../../../Analysis/ordinary-differential-equations/lyapunov-s-indirect-method/exists-unstable-of-has-fderiv-at.md)
- [Brouwer's fixed-point theorem for the standard simplex](../../../../Topology/algebraic-topology/brouwer-fixed-point-theorem/exists-fixed-point.md)

## Expansion

For $p' > p$ the comparison of the two conditions reduces to $2 + p + p' < 2 + 2p'$, that is $p < p'$. Both right-hand sides are below $1$, so control can evolve even when it lowers colony efficiency, $r' < r$. The reason is transmission: a heterozygous mutant queen passes $a$ to half of her sons but only to a quarter of her workers' sons (her grandsons), so shifting male production from workers to the queen raises the share of the mutant allele among males. The mating number drops out because, at leading order in the mutant frequency, a colony type with one mutant mate contributes offspring like a type with $n$ mutant mates in a fraction $1/n$ of fertilizations, and that $1/n$ cancels the factor $n$ in its relative frequency. When a coexistence regime occurs, the existence of a mixed equilibrium follows from Brouwer's fixed-point theorem applied to the frequency dynamics.

## Sources

- J. Olejarz, C. Veller and M. A. Nowak, "The evolution of queen control over worker reproduction in the social Hymenoptera", Ecology and Evolution 7 (2017), Sections 2 and 3.1, Conditions (1)–(2), <https://doi.org/10.1002/ece3.3324>, PMCID PMC5648666.
