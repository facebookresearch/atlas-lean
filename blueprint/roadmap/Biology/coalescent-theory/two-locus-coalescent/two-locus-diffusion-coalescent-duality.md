# Duality between the two-locus diffusion and the coalescent with recombination

For two loci with alleles $a/A$ and $b/B$ and scaled recombination rate $\rho$ ($2Nr_N \to \rho/2$, time in units of $2N$ generations), the allele frequencies and linkage disequilibrium $(p_a, p_b, D)$ of the two-locus Wright–Fisher model converge to the two-locus Wright–Fisher diffusion, whose generator has the recombination drift $-D(1 + \rho/2)\partial_D$ (Ohta and Kimura 1969; Mano 2013, generator (2.1), where $\rho = 4Nr$); and the joint genealogy of a sample at the two loci converges to the two-locus coalescent, in which each pair of lines merges at rate $1$ and each line carrying ancestral material at both loci splits at rate $\rho/2$ (Hudson 1983; Griffiths 1991; Mano 2013, rates (3.1)). The diffusion's generator is the [generator of the two-locus Wright–Fisher diffusion](../../../Biology/coalescent-theory/two-locus-coalescent/two-locus-generator.md), and for a sample of two the coalescent's rate matrix is the [rate matrix of the two-locus coalescent](../../../Biology/coalescent-theory/two-locus-coalescent/two-locus-rate.md). The target is the duality between them: for a sample of $n$ chromosomes drawn at time $t$, expected haplotype-sampling monomials of the diffusion equal expectations over the two-locus coalescent run for time $t$ from the sample, as a process-level identity derived from the two generators (Mano 2013, Lemma 3.1; Griffiths, Jenkins and Lessard 2016, Sections 3 and 6), with the covariance of coalescence times (Griffiths 1981) and the forward moment equations of Ohta and Kimura (1969) as its two sides.

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

- S. Mano, Duality between the two-locus Wright–Fisher diffusion model and the ancestral process with recombination, J. Appl. Probab. 50 (2013), 256–271, generator (2.1), rates (3.1) and Lemma 3.1, numbered as in arXiv:1201.5557v2 (journal numbering not confirmed). <https://arxiv.org/abs/1201.5557>
- R. C. Griffiths, P. A. Jenkins and S. Lessard, A coalescent dual process for a Wright–Fisher diffusion with recombination and its application to haplotype partitioning, Theor. Popul. Biol. 112 (2016), 126–138, Sections 3 and 6, numbered as in arXiv:1604.04145v2. <https://arxiv.org/abs/1604.04145>
- T. Ohta and M. Kimura, Linkage disequilibrium due to random genetic drift, Genet. Res. 13 (1969), 47–55.
- R. C. Griffiths, Neutral two-locus multiple allele models with recombination, Theor. Popul. Biol. 19 (1981), 169–186.
- R. R. Hudson, Properties of a neutral allele model with intragenic recombination, Theor. Popul. Biol. 23 (1983), 183–201. <https://doi.org/10.1016/0040-5809(83)90013-8>
- R. C. Griffiths, The two-locus ancestral graph, in Selected Proceedings of the Sheffield Symposium on Applied Probability, IMS Lecture Notes–Monograph Series 18 (1991), 100–117.
