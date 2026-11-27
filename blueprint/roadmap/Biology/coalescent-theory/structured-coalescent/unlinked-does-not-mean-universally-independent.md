# Genealogies at unlinked loci are conditionally independent given the pedigree

Coalescent likelihoods often treat unlinked loci as independent. In the fixed-pedigree model of Wakeley, King, Low and Ramachandran (2012, Methods), lineages percolate through one population pedigree by Mendelian transmission, and independent assortment is modelled by tracing each unlinked locus independently on the same pedigree, with free recombination between loci; hence, given the pedigree, the genealogies at unlinked loci are independent. The standard coalescent applied separately to unlinked loci instead implicitly draws a new random pedigree for every locus (their Introduction). Because all loci share one pedigree, independence of the genealogies at unlinked loci is a statement conditional on that pedigree. That they need not be independent once the pedigree is regarded as random and averaged over is shown, for coalescence times under partial selfing, in [selfing keeps unlinked coalescence times correlated](../two-locus-coalescent/linked-coalescence-times-under-partial-selfing/selfing-keeps-unlinked-coalescence-times-correlated.md).

## Depends on

- [Genealogies within a fixed pedigree](../../../Biology/coalescent-theory/structured-coalescent/fixed-pedigree-versus-averaged-genealogy.md)

## Expansion

1. Conditional independence of genealogies at unlinked loci given the pedigree, from independent tracing on a common pedigree.
2. The contrast with applying the coalescent separately to each locus, which corresponds to an independent pedigree per locus.
3. The consequences for products of single-locus likelihoods.

## Sources

- J. Wakeley, L. King, B. S. Low and S. Ramachandran, Gene genealogies within a fixed pedigree, and the robustness of Kingman's coalescent, Genetics 190 (2012), 1433–1445, Introduction and Methods. <https://doi.org/10.1534/genetics.111.135574>
