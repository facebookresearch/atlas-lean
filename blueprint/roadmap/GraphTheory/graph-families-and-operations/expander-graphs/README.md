# Expander graphs

Expanders are sparse graphs that behave like random graphs. Two measures appear here: vertex expansion ($C$-expanders, uniform vertex expanders) and spectral expansion, where a $d$-regular graph on $N$ vertices has parameter $\lambda$ when its random-walk matrix shrinks every vector orthogonal to the constants by the factor $\lambda$. Spectral expansion controls edge counts (the expander mixing lemma), cannot beat $2\sqrt{d - 1}/d$ asymptotically (Alon-Boppana; Ramanujan graphs attain it), and makes a $t$-step random walk behave like $t$ independent samples (the hitting property and the Chernoff bound for expander walks).

- [External neighbourhood](external-neighbor-set.md)
- [Membership in the external neighbourhood](mem-external-neighbor-set.md)
- [The external neighbourhood is disjoint from the set](external-neighbor-set-disjoint.md)
- [External neighbours have a neighbour in the set](exists-adj-of-mem-external-neighbor-set.md)
- [C-expander](is-cexpander.md)
- [The parameter of a C-expander is positive](pos.md)
- [Small sets expand in a $C$-expander](small-expansion.md)
- [Large disjoint sets in a C-expander span an edge](large-edge.md)
- [Uniform vertex expander](is-uniform-vertex-expander.md)
- [The parameter of a uniform vertex expander is positive](pos-2.md)
- [Small sets expand in a uniform vertex expander](small-expansion-2.md)
- [Bipartite Ramanujan graphs of every degree](exists-bipartite-ramanujan.md)
- [Spectral bound on the vectors orthogonal to the constants](is-spectral-bound.md)
- [Spectral expander](is-spectral-expander.md)
- [The complete graph is a spectral expander](is-spectral-expander-top.md)
- [Edge count as a bilinear form](card-interedges-eq-indicator-dot-product.md)
- [Expander mixing lemma for matrices](abs-indicator-dot-product-mul-vec-sub-le.md)
- [Expander mixing lemma](expander-mixing-lemma.md)
- [Expander mixing lemma, unnormalised form](abs-card-interedges-sub-le.md)
- [Spectral expanders have edge expansion, from the mixing lemma](spectral-edge-expansion.md)
- [Laplacian Rayleigh quotient of a spectral expander](laplacian-rayleigh-quotient.md)
- [Spectral expanders have edge expansion, through Cheeger's inequality](spectral-edge-expansion-via-cheeger.md)
- [Independent sets in spectral expanders are small](independent-sets-are-small.md)
- [Elementary lower bound on the spectral parameter](elementary-spectral-lower-bound.md)
- [Alon-Boppana bound](alon-boppana.md)
- [Probability of an event for a random walk on a regular graph](walk-prob.md)
- [Random-walk probabilities have total mass one](walk-prob-true.md)
- [Hitting property of expander walks](hitting-property-of-expander-walks.md)
- [Chernoff bound for expander walks](chernoff-bound-expander-walk.md)
- [Spectral expanders have logarithmic diameter](logarithmic-diameter.md)

## Related topics

- [Graph Laplacians and Cheeger's inequality](../../algebraic-graph-theory/part-01/graph-laplacians-and-cheeger-s-inequality/README.md): spectral expansion: Cheeger's inequality ties $\lambda_2$ to edge expansion.
- [Interlacing families of polynomials](../../../Algebra/zeros-of-polynomials/interlacing-families-of-polynomials/README.md): the method behind bipartite Ramanujan graphs of every degree.
- [Zig-zag product and explicit expanders](../zig-zag-product-and-explicit-expanders/README.md): how constant-degree spectral expanders are built from one small expander by squaring and zig-zag products.
- [Conductance and Cheeger's inequality](../../algebraic-graph-theory/part-02/conductance-and-cheeger-s-inequality/README.md): the combinatorial face of spectral expansion, edge expansion bounded by the second Laplacian eigenvalue.
- [Random walks on finite groups](../../../Probability/random-walks/random-walks-on-finite-groups/README.md): Cayley graphs, whose random walks mix fast exactly when the graph is a spectral expander.
- [Mixing times of Markov chains](../../../Probability/markov-chains/mixing-times-of-markov-chains/README.md): the spectral gap $1 - \lambda$ controls the mixing time of the random walk.
- [Explicit sum-product expanders over prime fields](../../../Combinatorics/additive-combinatorics/sumsets-inverse-theorems/explicit-sum-product-expanders-over-prime-fields/README.md): explicit expansion from arithmetic combinatorics.
- [Pseudorandomness and one-way functions](../../../TheoryOfComputation/pseudorandomness-and-one-way-functions/README.md): expanders are pseudorandom graphs; walks on them save random bits in derandomization.
