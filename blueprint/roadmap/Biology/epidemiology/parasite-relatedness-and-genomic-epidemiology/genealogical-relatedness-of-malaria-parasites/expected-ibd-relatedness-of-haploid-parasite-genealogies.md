# Expected IBD relatedness of haploid parasite genealogies

Consider haploid parasites in which two genetically unrelated haploid parents fuse into a diploid zygote in the mosquito and a single meiosis inside the oocyst produces four haploid products; at a locus where the parents differ, exactly two products carry each parental allele. Define the relatedness $r$ of two parasites as the expected fraction of the genome they share identical by descent (IBD) from the parents of the pedigree, and assume outcrossing to unrelated parasites outside the pedigree, as in the outcrossed pedigrees considered. Then:

1. **Parent–child.** A progeny inherits each locus from a given parent with probability $1/2$, so $r_{\mathrm{PC}} = 1/2$.
2. **Full siblings** (from two different oocysts of the same parental pair). The inherited parents at a locus are independent fair coin flips, so the two progeny agree with probability $r_{\mathrm{FS}} = 1/2$.
3. **Meiotic siblings** (two distinct products of the same oocyst). Two products drawn without replacement from the four carry the same parental allele with probability $\binom{2}{2} \cdot 2 / \binom{4}{2} = 2/6$, so $r_{\mathrm{MS}} = 1/3$.
4. Each further outcrossed meiosis separating the two parasites halves the expected relatedness: grandparent–grandchild and half siblings have $r = 1/4$, great-grandparent and half avuncular $r = 1/8$; full avuncular and full cousins have $r = 1/4$ and $1/8$ when the parental F1 parasites are full siblings, but $r = 1/6$ and $1/12$ when they are meiotic siblings.

## Proof sketch

In a haploid organism a progeny is not guaranteed to carry half of each parent's genome (only half in expectation), unlike in diploids. Linearity of expectation over loci turns the locus-level probabilities into genome-wide expected IBD fractions; recombination changes the variance and the segment structure, not the mean. Meiotic siblings share less than full siblings because the four products of one meiosis carry each parental allele exactly twice, which creates negative dependence between products: given that one product carries the allele of parent 1, only one of the remaining three does. Since full siblings and parent–child pairs share the same mean relatedness, distinguishing them requires the distribution of IBD segments, not only the genome-wide fraction.

## Sources

- W. Wong, L. Wang, S. F. Schaffner, X. Li, I. Cheeseman, T. J. C. Anderson, A. Vaughan, M. Ferdig, S. K. Volkman, D. L. Hartl and D. F. Wirth, "MalKinID: A classification model for identifying malaria parasite genealogical relationships using identity-by-descent", *Genetics* 229 (2025), iyae197, Introduction and Table 1, <https://doi.org/10.1093/genetics/iyae197> (PMC11796457).
