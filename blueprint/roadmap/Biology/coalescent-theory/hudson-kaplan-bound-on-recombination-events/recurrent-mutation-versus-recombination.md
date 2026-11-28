# Recurrent mutation can mimic recombination in the four-gamete test

Under the infinite-sites model each site mutates at most once in the history of the sample, so on a single genealogy every pair of sites is compatible and shows at most three of the four two-site haplotypes; observing all four gametes then implies a recombination between the sites, and Hudson and Kaplan's $R_m$ counts the recombination events that can be parsimoniously inferred in this way (Hudson and Kaplan 1985, Abstract). With recurrent or back mutation a single genealogy can produce all four gametes. For example, take four sequences with genealogy $((a, b), (c, d))$, let the first site mutate once on the branch above the cherry $\{a, b\}$, and let the second site mutate twice, once on the pendant branch to $a$ and once on the pendant branch to $c$. Writing derived alleles as $1$, the haplotypes are $a = 11$, $b = 10$, $c = 01$ and $d = 00$: all four gametes, with no recombination. Hence a positive $R_m$ is evidence of recombination only under a model without homoplasy; under a finite-sites mutation model it also reflects repeated mutation at the same site.

## Depends on

- [Four-gamete condition for two sites](../../../Biology/coalescent-theory/hudson-kaplan-bound-on-recombination-events/four-gametes.md)
- [Hudson and Kaplan's $R_m$](../../../Biology/coalescent-theory/hudson-kaplan-bound-on-recombination-events/rm.md)
- [$R_m$ is a lower bound on the size of a valid breakpoint set](../../../Biology/coalescent-theory/hudson-kaplan-bound-on-recombination-events/rm-le-card-of-is-breakpoint-set.md)
- [Perfect phylogeny and the four-gamete condition](../../../Biology/phylogenetics/splits-compatibility-ultrametrics-and-upgma/exists-perfect-phylogeny-iff.md)

## Expansion

1. The four-gamete condition and $R_m$ as a lower bound on the number of recombination breakpoints.
2. Compatibility of all site pairs on one genealogy under infinite sites, from the perfect-phylogeny characterization.
3. The explicit homoplasy example with four gametes and no recombination.
4. The probability of a site with more than one mutation under a finite-sites model, as a function of the mutation rate and the genealogy, as a separate statement.

## Sources

- R. R. Hudson and N. L. Kaplan, Statistical properties of the number of recombination events in the history of a sample of DNA sequences, Genetics 111 (1985), 147–164, Abstract. <https://doi.org/10.1093/genetics/111.1.147>
