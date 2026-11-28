# Expected spectra on demographic graphs by dynamic programming (momi2)

Kamm, Terhorst, Durbin and Song (2020) compute the exact expected infinite-sites joint site-frequency spectrum for populations related by a directed acyclic graph with size changes, exponential growth, population splits and instantaneous admixture pulses. They replace the coalescent by the continuous-time Moran model, which induces the same sampling distribution with a much smaller state space (Section 2.3), and compute expectations by a dynamic program in the spirit of a junction-tree algorithm: conditional likelihoods of the leaf allele counts given ancestral allele counts are lifted along branches by the Moran transition (their Lemma 1), transformed at an admixture pulse (Lemma 2), and combined at a split whose children lie in separate clusters (Lemma 3) or in the same cluster (Lemma 4); Section 3.1 runs the algorithm on a three-population example with one pulse, and Appendix A.2 proves the formulas and the correctness of the algorithm. The same recursion computes rank-one tensor products of the expected spectrum, and hence general linear functionals as sums of these, at the cost of a single entry.

## Expansion

1. The demographic graph: populations, branches with size histories, splits and admixture pulses, and the infinite-sites sampling model.
2. Equality of the Moran-model and coalescent sampling distributions for allele counts along a branch.
3. The four update rules for conditional likelihoods (Lemmas 1–4) and the order in which the junction-tree recursion applies them.
4. The correctness of the recursion for the expected spectrum (Appendix A.2), by induction over the graph.
5. Linear functionals of the expected spectrum through rank-one tensor products.

## Sources

- J. Kamm, J. Terhorst, R. Durbin and Y. S. Song, Efficiently inferring the demographic history of many populations with allele count data, J. Amer. Statist. Assoc. 115 (2020), 1472–1487, Sections 2.3 and 3 and Appendix A.2. <https://doi.org/10.1080/01621459.2019.1635482>
