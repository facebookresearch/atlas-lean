# Graph limits

Dense graph limits in the sense of Lovász and Szegedy: homomorphism densities $t(F, G)$ of a graph $F$ in a (weighted) graph $G$, the cut norm and cut distance, the counting lemma, the Frieze–Kannan weak regularity lemma, convergent graph sequences, graphons as their limits, and compactness of the graphon space.

Homomorphism densities of finite graphs:

- [Weight of a map into a weighted graph](hom-weight.md)
- [Homomorphism density](hom-density.md)
- [Edge weight of a simple graph](adj-weight.md)
- [Simple-graph weights lie in the unit interval](adj-weight-mem-unit-interval.md)
- [Homomorphism density counts homomorphisms](hom-density-adj-weight.md)
- [Homomorphism densities are normalized](hom-density-bot.md)
- [Homomorphism densities are nonnegative](hom-density-nonneg.md)
- [Homomorphism densities are at most one](hom-density-le-one.md)

The cut norm and the counting lemma:

- [Unnormalized cut norm](cut-max.md)
- [Cut norm](cut-norm.md)
- [Nonnegativity of the cut norm](cut-norm-nonneg.md)
- [Weighted sums are bounded by subset sums](exists-abs-sum-mul-le.md)
- [Bilinear forms are bounded by the cut norm](abs-sum-sum-mul-le-cut-max.md)
- [One telescoping step of the counting lemma](card-sq-mul-abs-sum-le.md)
- [Counting lemma](abs-hom-density-sub-hom-density-le.md)

Weak regularity:

- [Partition average of a weighted graph](partition-average.md)
- [L² norm of a weighted graph](kernel-l2-norm.md)
- [Block-constant functions](is-block-constant.md)
- [The partition average is block-constant](is-block-constant-partition-average.md)
- [Orthogonality of the partition average](sum-sub-partition-average-mul-eq-zero.md)
- [Energy of a partition](partition-energy.md)
- [The energy is bounded by the total mass](partition-energy-le.md)
- [Common refinement relation](refine-setoid.md)
- [Refinement by two sets](refine-by.md)
- [Refinement multiplies the number of classes by at most four](card-refine-by-parts-le.md)
- [Energy increment](sq-sum-sub-partition-average-le.md)
- [One refinement step](exists-refinement-of-lt-cut-norm.md)
- [Weak regularity lemma (Frieze–Kannan)](exists-cut-norm-sub-partition-average-le.md)

Graphons and convergence:

- [Homomorphism density in a graphon](graphon-hom-density.md)
- [Measurable rectangles of the unit square](cut-pair.md)
- [Cut norm of a kernel](graphon-cut-norm.md)
- [Measure-preserving maps of the unit interval](unit-interval-mp.md)
- [Cut distance of graphons](cut-distance.md)
- [Counting lemma for graphons](abs-graphon-hom-density-sub-le.md)
- [Convergent graph sequence](is-convergent-graph-sequence.md)
- [Lovász–Szegedy limit theorem](exists-graphon-limit.md)
- [Every graphon is a graph limit](exists-graph-sequence-tendsto.md)
- [Compactness of the graphon space](exists-subseq-tendsto-cut-distance.md)
- [Left convergence is cut-distance convergence](tendsto-graphon-hom-density-iff-tendsto.md)
- [Uniqueness of the limit](cut-distance-eq-zero-iff.md)

## Related topics

- [Finitely forcible graphons](../finitely-forcible-graphons/README.md): graphons determined by finitely many subgraph densities, in the same graphon convention; Lovász's finitely forcible optimum conjecture and its refutation.
- [Sidorenko's conjecture](../../extremal-graph-theory/sidorenko-s-conjecture/README.md): an extremal problem for homomorphism densities of bipartite graphs, posed for graphons.
- [Kim–Vu polynomial concentration](../../../Probability/concentration-inequalities/kim-vu-polynomial-concentration/README.md): concentration of subgraph counts in $G(n, p)$, the kind of estimate behind $t(F, G(n, p)) \to p^{|E(F)|}$, i.e. the convergence of $G(n, p)$ to the constant graphon $p$.
- [Triangle density and flag algebras](../../extremal-graph-theory/triangle-density-and-flag-algebras/README.md): Razborov's flag algebras work with induced subgraph densities, which carry the same information as the homomorphism densities used here and pass to graph limits; Razborov used them to determine the minimal triangle density at a given edge density.
- [Threshold for triangles](../threshold-for-triangles/README.md): sparse random graphs, where $p \to 0$ and the dense limit is the zero graphon; subgraph counts must then be normalized differently.
- [Gowers uniformity norms](../../../Combinatorics/additive-combinatorics/progressions-dense-sets/gowers-uniformity-norms/README.md): averages over arithmetic cubes, the arithmetic analogue of homomorphism densities; $\|1_A\|_{U^2}^4$ is the four-cycle density of the kernel $1_A(x + y)$, and the generalized von Neumann theorem plays the role of the counting lemma.
