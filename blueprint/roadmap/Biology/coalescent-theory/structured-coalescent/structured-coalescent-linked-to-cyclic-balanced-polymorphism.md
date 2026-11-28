# Structured coalescent at a neutral site linked to a cyclically fluctuating balanced polymorphism

**Setting.** A diploid population of size $N$ carries a balanced biallelic polymorphism (alleles $W$ and $S$) whose frequency follows a periodic trajectory $\pi_0,\dots,\pi_{G-1}$ of period $G$ generations. For example, $g$ generations of winter favour $W$ and $g$ generations of summer favour $S$ ($G=2g$), with stable polymorphism under marginal overdominance. A neutral biallelic site at recombination probability $r$ from the selected site mutates symmetrically at rate $u$ per generation, and the selected site mutates at rate $u$ as well. Assume coalescence, mutation and recombination are rare per cycle, so the background-structured coalescent of two lineages (states $(2,0)$, $(0,2)$, $(1,1)$ and coalesced) can be replaced by its cycle average, a time-homogeneous chain with rates:

$$c=\frac1G\sum_{t=0}^{G-1}\frac1{2N\pi_t}=\frac1{2N\tilde p}\quad\text{(coalescence within a background)},$$

$$m=u\Big(\frac1{\tilde p}-1\Big)+r\,\bar p\quad\text{(switching background, per lineage)},$$

where $\tilde p$ is the harmonic mean and $\bar p$ the arithmetic mean of $\pi_t$ over the cycle. These forms of $c$ and of the mutation part of $m$ hold for each allele in **symmetric** cycles, in which $\pi_t$ and $1-\pi_t$ have the same harmonic mean and $\bar p=1/2$.

**Mean coalescence times.** First-step analysis gives

$$\mathbb E[T_{(2,0)}]=\mathbb E[T_{(0,2)}]=\frac2c=4N\tilde p,\qquad \mathbb E[T_{(1,1)}]=4N\tilde p+\frac1{r+2u(1/\tilde p-1)} .$$

**Heterozygosity.** With symmetric two-allele mutation and an exponential coalescence time of mean $T$, the probability that two copies differ is

$$\mathbb E[H]=\frac12\Big(1-\frac1{1+4uT}\Big),$$

and with Hardy-Weinberg sampling at time $t$, $\mathbb E[H_t]\approx\pi_t^2H_{(2,0)}+2\pi_t(1-\pi_t)H_{(1,1)}+(1-\pi_t)^2H_{(0,2)}$. For $u\ll r$, to leading order in $u$,

$$\mathbb E[H_t]\approx8N\tilde p\,u+\frac{4u\,\pi_t(1-\pi_t)}{r}.$$

Compared with the neutral value $4Nu$, diversity is raised near the selected site and depressed further away. The crossover is at $r^*=\pi_t(1-\pi_t)/[N(1-2\tilde p)]$, and the valley floor is $H_{\min}=\frac12[1-1/(1+16uN\tilde p)]\approx8uN\tilde p$, a change of $100(2\tilde p-1)$ percent. The fluctuations enter only through $\tilde p\le\bar p=1/2$, and the profile depends on $r$ and $N$ only through $Nr$.

**Explicit harmonic mean.** For the symmetric seasonal model with $h\approx\tfrac12$ and $\pi_t$ near $\tfrac12$, the odds grow geometrically, $\pi_i/(1-\pi_i)\approx\varrho^{\,i-g/2}$ for $0\le i\le g$ with $\varrho=(4+3s)/(4+s)$, and

$$\tilde p\approx\frac{2g(\varrho-1)}{2g(\varrho-1)+(\varrho+1)(\varrho^{g/2}-\varrho^{-g/2})}.$$

## Depends on

- [Coalescent in an allelic background with a given frequency path](../site-frequency-spectrum-under-variable-populatio/coalescent-in-an-allelic-background-with-a-given.md)

## Proof depends on

- [First-step equations for mean coalescence time](first-step-equations.md)
- [Coalescent in an allelic background with a given frequency path](../site-frequency-spectrum-under-variable-populatio/coalescent-in-an-allelic-background-with-a-given.md)
- [Moment generating function of the exponential distribution](../../../Probability/random-walks/gumbel-limit-of-the-maximal-segment-score/mgf-id-exp-measure.md)

## Expansion

In the averaged chain, state $(2,0)$ leaves at total rate $c+2m$: it coalesces with probability $c/(c+2m)$ or moves to $(1,1)$. State $(1,1)$ moves to a same-background state at rate $2m$. Hence $T_{20}=1/(c+2m)+[2m/(c+2m)]T_{11}$ and $T_{11}=1/(2m)+T_{20}$, which solve to the stated formulas. The heterozygosity formula is $\Pr[\text{odd number of mutations}]=\frac12(1-\mathbb E[e^{-4uT}])$ evaluated for exponential $T$. Note that $T_{(1,1)}$ is not exponential, so this step is an approximation there. The harmonic-mean formula sums $1/[\pi(1-\pi)]=R+R^{-1}+2$ with $R=\varrho^{\,i-g/2}$ over $i=1,\dots,g$ as two geometric series. Because $\tilde p$ ignores the order of frequencies in the cycle, cycles of different lengths can leave the same footprint at tight linkage. Loose linkage, where lineages switch background within a cycle, needs the [hitchhiking correction](../../population-genetics/effective-population-size/hitchhiking-effective-size-under-cyclic-balancing-selection.md).

## Sources

- M. J. Wittmann, S. Mousset and J. Hermisson, "Modeling the genetic footprint of fluctuating balancing selection: from the local to the genomic scale", Genetics (2023), iyad022, <https://doi.org/10.1093/genetics/iyad022>; equation numbers as in the preprint version, <https://doi.org/10.1101/2022.07.15.500223>. Equations (3), (5)-(19) ("Analytical approximation step 1: structured coalescent"), (28)-(29) (diversity valley), and Appendix 1 (geometric odds approximation, Equations (A1)-(A4)) and Appendix 2 (heterozygosity with back mutation).
