# Two-locus haplotype frequencies are identified by genotype frequencies

At two biallelic loci, let $h = (h_{AB}, h_{Ab}, h_{aB}, h_{ab})$ be haplotype frequencies on the probability simplex, and suppose genotypes are
formed by uniting two independently drawn haplotypes (Hardy–Weinberg proportions at the haplotype level). Each double
homozygote can arise only from two copies of one haplotype, so

$$\mathbb P(AABB) = h_{AB}^2, \quad \mathbb P(AAbb) = h_{Ab}^2, \quad \mathbb P(aaBB) = h_{aB}^2, \quad \mathbb P(aabb) = h_{ab}^2,$$

and $h_x = \sqrt{\mathbb P(xx)}$ for each haplotype $x$. Hence the map from $h$ to the genotype law is injective, and the
[linkage disequilibrium](linkage-diseq.md) $D = h_{AB} h_{ab} - h_{Ab} h_{aB}$ is identified, although the double heterozygote $AaBb$, with probability
$2(h_{AB} h_{ab} + h_{Ab} h_{aB})$, does not reveal its phase. This is identification at the population level; it says nothing about the
shape of the likelihood of a finite sample, which can have several stationary points.

## Depends on

- [Linkage disequilibrium](linkage-diseq.md)

## Sources

- W. G. Hill, "Estimation of linkage disequilibrium in randomly mating populations", Heredity 33 (1974), 229–239, <https://doi.org/10.1038/hdy.1974.89> (two-locus genotype probabilities under random mating). The identification is derived above.
