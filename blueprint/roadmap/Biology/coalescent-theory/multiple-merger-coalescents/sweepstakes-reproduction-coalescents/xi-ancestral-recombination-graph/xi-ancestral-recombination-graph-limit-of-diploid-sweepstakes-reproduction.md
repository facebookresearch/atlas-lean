# The Ξ-ancestral recombination graph as the limit of diploid multi-locus sweepstakes reproduction

**Population model.** A population has $N$ diploid individuals, each carrying two copies of a chromosome with $L$ loci. In each reproduction event two random parents produce a random number $\Psi^{(N)}$ of offspring, which replace as many random individuals. Each child inherits one chromosome from each parent by Mendelian segregation, with a crossover between loci $\ell$ and $\ell+1$ with probability $r^{(N)}_\ell$. Let

$$c_N = \mathbb{E}\big[\Psi^{(N)}(\Psi^{(N)}+3)\big]/\big(N(N-1)\big),$$

which is four times the probability that two random chromosomes coalesce in one event. Assume:

1. **Separation of time scales:** $\dfrac{c_N}{\mathbb{E}[\Psi^{(N)}/N]} \to 0$;
2. **Sagitov-type tail condition:** for a probability measure $\Lambda$ on $[0,1]$ and all continuity points $x\in(0,1]$, $\dfrac{1}{c_N}\Pr(\Psi^{(N)} > Nx) \to \int_{(x,1]} y^{-2}\,\Lambda(dy)$;
3. **Recombination scaling:** $r_\ell^{(N)} \sim \dfrac{c_N}{4\,\mathbb{E}[\Psi^{(N)}/N]}\,r^{(\ell)}$ with fixed $r^{(\ell)} \ge 0$.

**Ancestral configurations.** Sample $n$ chromosomes. A configuration is a collection $\zeta = \{C_1,\dots,C_b\}$ of ancestral chromosomes, where $C_i = (\tilde C_{i,1},\dots,\tilde C_{i,L})$ lists, for each locus, the sampled chromosomes to which $C_i$ is ancestral there. For each locus the sets $\tilde C_{\cdot,\ell}$ partition $[n]$, allowing empty blocks. The possible transitions are:

- **pairmerge** of two ancestral chromosomes, taking the locuswise union;
- **groupmerge** into up to four simultaneous groups $J_1,\dots,J_4$, the four parental chromosomes of one sweepstakes pair, in which at least one group has $\ge 3$ members or at least two groups have $\ge 2$;
- **recomb** of chromosome $i$ between loci $\ell$ and $\ell+1$, splitting it into a left part and a right part.

**Theorem.** Under conditions 1–3, the ancestral process $\xi^{n,N}$ of the sample, run for $\lfloor 4t/c_N\rfloor$ reproduction events up to time $t$, converges as $N\to\infty$ to the continuous-time Markov chain $\xi(t)$ with rates

$$q_{\zeta,\zeta'} = \begin{cases} C_{b;2} & \zeta' = \mathsf{pairmerge}(\zeta),\\ r^{(\ell)} & \zeta' = \mathsf{recomb}_{\cdot,\ell}(\zeta),\\ C_{b;|J|} & \zeta' = \mathsf{groupmerge}_J(\zeta),\end{cases}$$

where for group sizes $k = (k_1,\dots,k_r)$ with $|k| = \sum k_j$ and $s = b - |k|$ untouched lineages,

$$C_{b;k;s} = \Lambda(\{0\})\,\mathbf{1}_{\{r=1,\,k_1=2\}} + 4\sum_{l=0}^{s\wedge(4-r)}\binom{s}{l}\frac{(4)_{r+l}}{4^{|k|+l}}\int_{(0,1]}x^{|k|+l}(1-x)^{s-l}\,\frac{\Lambda(dx)}{x^2}.$$

$(4)_m$ denotes the falling factorial. This limit is the **$\Xi$-ancestral recombination graph**. At a single locus it reduces to a $\Xi$-coalescent with simultaneous multiple mergers into at most four groups. With $\Lambda = \delta_0$ it reduces to the usual ancestral recombination graph.

## Depends on

- [The Ξ-coalescent rate matrix on partitions of a finite sample](../../../coalescents/xi-coalescent-partition-valued-ctmc-and-restrict.md)
- [Coalescent with recombination: ancestral-material state space and generator](../../../two-locus-coalescent/coalescent-with-recombination-ancestral-material.md)

## Proof depends on

- [Möhle's lemma on Markov chains with two time scales](../../../../../Probability/markov-chains/finite-markov-chains/mohle-s-separation-of-timescales-lemma-for-finit.md)
- [Möhle–Sagitov conditions for a Λ-coalescent limit](../../coalescent-limits-of-cannings-models/mohle-sagitov-lambda.md)

## Expansion

In a large sweepstakes event a fraction $x$ of the population descends from one parental pair. Each affected lineage picks one of the four parental chromosomes uniformly, so up to four simultaneous mergers occur. The factor $(4)_{r+l}/4^{|k|+l}$ can be read as the probability that the $r$ merging groups and $l$ unchanged but affected lineages land on distinct parental chromosomes. Condition 1 makes sampled chromosomes that share an individual separate quickly compared with coalescence, so the limit can ignore the pairing into diploid individuals. Condition 3 puts recombination on the coalescent time scale. A one-step example is $\Pr(\Psi^{(N)} = \lceil\psi N\rceil) = c/N^2$, otherwise $\Psi^{(N)} = 1$, which gives a Dirac-type $\Lambda$ concentrated at $\psi$. Because linked loci can be caught in the same multiple-merger event, the genealogies at different loci are correlated through these simultaneous mergers as well as through linkage.

## Sources

- M. Birkner and J. Blath, "Genealogies and inference for populations with highly skewed offspring distributions", in *Probabilistic Structures in Evolution* (E. Baake and A. Wakolbinger, eds.), EMS Series of Congress Reports, EMS Press (2021), 151–178, <https://doi.org/10.4171/ECR/17-1/8>; preprint arXiv:1912.07977, <https://doi.org/10.48550/arXiv.1912.07977>: Section "Multiple loci, diploidy and Ξ-coalescents" (diploid model, Ξ-ARG configurations and the convergence proposition).
- M. Birkner, J. Blath and B. Eldon, "An ancestral recombination graph for diploid populations with skewed offspring distribution", *Genetics* 193 (2013), 255–290, Theorem 1.3, <https://doi.org/10.1534/genetics.112.144329>. Its fixed-fraction case, Theorem 1.2, is [Diploid ancestral recombination graph with simultaneous multiple mergers](../diploid-sweepstakes-coalescents/diploid-ancestral-recombination-graph-with-simultaneous-multiple-mergers.md).
