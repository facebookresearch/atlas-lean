# Duality between the two-locus diffusion and the coalescent with recombination

For two loci with alleles $a/A$ and $b/B$ and scaled recombination rate $\rho$ ($2Nr_N \to \rho/2$, time in units of $2N$ generations), the allele frequencies and linkage disequilibrium $(p_a, p_b, D)$ of the two-locus Wright–Fisher model converge to the two-locus Wright–Fisher diffusion, whose generator has the recombination drift $-D(1 + \rho/2)\partial_D$ (Birkner, Fact 4.2.1 and (4.7), after Ohta and Kimura); and the joint genealogy of a sample at the two loci converges to the two-locus coalescent, in which each pair of lines merges at rate $1$ and each line carrying ancestral material at both loci splits at rate $\rho/2$ (Theorem 4.3.1). The diffusion's generator is the [generator of the two-locus Wright–Fisher diffusion](../../../Biology/coalescent-theory/two-locus-coalescent/two-locus-generator.md), and for a sample of two the coalescent's rate matrix is the [rate matrix of the two-locus coalescent](../../../Biology/coalescent-theory/two-locus-coalescent/two-locus-rate.md). The target is the duality between them: for a sample of $n$ chromosomes drawn at time $t$, expected haplotype-sampling monomials of the diffusion equal expectations over the two-locus coalescent run for time $t$ from the sample, as a process-level identity derived from the two generators, with the covariance of coalescence times (Proposition 4.3.2) and the forward moment equations as its two sides.

## Depends on

- [Generator of the two-locus Wright–Fisher diffusion](../../../Biology/coalescent-theory/two-locus-coalescent/two-locus-generator.md)
- [Rate matrix of the two-locus coalescent](../../../Biology/coalescent-theory/two-locus-coalescent/two-locus-rate.md)

## Expansion

1. The two-locus Wright–Fisher model with recombination and its diffusion limit, with the generator in the coordinates $(p_a, p_b, D)$.
2. The joint genealogy at the two loci and its limit, the two-locus coalescent with merging at rate $1$ and splitting at rate $\rho/2$.
3. The duality function: sampling probabilities of haplotype configurations as polynomials in the haplotype frequencies.
4. The generator identity between the two-locus diffusion and the two-locus coalescent, and the duality for all $t \ge 0$.
5. The covariance of coalescence times and the moment equations for $D^2$ as the two sides of the duality.

## Sources

- M. Birkner, *Stochastic population models*, lecture notes, Johannes Gutenberg-Universität Mainz, 2025/26, Sec. 4.2–4.3: Fact 4.2.1, generator (4.7), Theorem 4.3.1 and Proposition 4.3.2.
