# Mathematical Biology

Mathematical biology models populations, genomes, and biochemical networks, from coalescents and reaction dynamics to the algorithms that read biological sequences.

[Population genetics](population-genetics/README.md) follows allele frequencies under drift, selection and mutation.
Over half of it is the [diffusion theory](population-genetics/diffusion-theory/README.md) of the Wright–Fisher
diffusion, from Kimura's fixation probability $(1 - e^{-2\sigma x})/(1 - e^{-2\sigma})$ for an allele at frequency
$x$ with scaled selection coefficient $\sigma = 2Ns$ to Wright's beta stationary law under two-way mutation, and the
[Ewens sampling formula](population-genetics/ewens-sampling-formula-and-the-chinese-restauran/README.md) gives the law
of the allelic partition of a sample under the neutral infinite-alleles model.
[Coalescent theory](coalescent-theory/README.md) traces genealogies backward in time: under
[Kingman's coalescent](coalescent-theory/kingman-s-coalescent-and-watterson-s-estimator/README.md) Watterson's
estimator of $\theta$ is unbiased, and the
[multispecies coalescent](coalescent-theory/multispecies-coalescent/README.md) has an anomaly zone, where a gene tree
that disagrees with the species tree is more probable than the one that agrees.

[Bioinformatics](bioinformatics/README.md) is the largest field, with about a sixth of the articles, and over half of
it is [sequence alignment](bioinformatics/sequence-alignment/README.md), from Needleman–Wunsch and Smith–Waterman to
affine-gap, linear-space and wavefront alignment and profile hidden Markov models.
[Phylogenetics](phylogenetics/README.md) reconstructs trees from sequences, with the
[Jukes–Cantor model](phylogenetics/jukes-cantor-model/README.md), neighbor joining and
[Felsenstein's pruning algorithm](phylogenetics/felsenstein-s-pruning-algorithm/README.md).
[Statistical genetics](statistical-genetics/README.md) treats genome-wide association studies, with
[LD score regression](statistical-genetics/ld-score-regression/README.md) and Mendelian randomization;
[population structure](population-structure/README.md) uses Patterson's f-statistics and admixture graphs;
[quantitative genetics](quantitative-genetics/README.md) has Fisher's decomposition of genetic variance; and in
[systems biology](systems-biology/README.md) the
[deficiency-zero theorem](systems-biology/complex-balancing-and-the-deficiency-zero-theore/README.md) gives a weakly
reversible mass-action network of deficiency zero exactly one equilibrium in each positive stoichiometric
compatibility class.

- [Population genetics](population-genetics/README.md)
- [Coalescent theory](coalescent-theory/README.md)
- [Detecting natural selection](detecting-selection/README.md)
- [Population structure and admixture](population-structure/README.md)
- [Phylogenetics](phylogenetics/README.md)
- [Quantitative genetics](quantitative-genetics/README.md)
- [Statistical genetics](statistical-genetics/README.md)
- [Cancer genomics](cancer-genomics/README.md)
- [Bioinformatics](bioinformatics/README.md)
- [Systems biology](systems-biology/README.md)
- [Population and evolutionary dynamics](population-dynamics/README.md)
- [Reaction–diffusion and pattern formation](pattern-formation/README.md)
- [Mathematical epidemiology](epidemiology/README.md)
