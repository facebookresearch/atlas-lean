# Noncrossing pair partitions and the Catalan count

A *pair partition* of $\{1, \dots, n\}$ is a set partition all of whose blocks have two elements;
it is *noncrossing* if no two blocks $\{a, c\}$ and $\{b, d\}$ interleave as $a < b < c < d$. There
are $C_k = \frac{1}{k+1}\binom{2k}{k}$ noncrossing pair partitions of $\{1, \dots, 2k\}$ and none
on an odd number of points. This is the combinatorial core of the moment method for Wigner
matrices, where the equivalence classes, under relabelling of the letters, of the Wigner words that
survive in $\frac{1}{N}\mathbb{E}\operatorname{tr} X_N^{k}$ (for $X_N = Y_N/\sqrt{N}$, with $Y_N$ an
$N \times N$ Wigner matrix whose entries are centred with variance one) are indexed by noncrossing
pair partitions, and of
the free central limit theorem, whose limit moments count the same partitions; both identify the
limit law as the semicircle distribution.

The proof encodes a pair partition by its partner map, a nested fixed-point-free involution, and
splits off the block containing the first point: if $1$ is paired with $j + 2$, the $j$ points
inside that arc and the points to its right carry independent noncrossing pairings. This gives
the Catalan recursion $M(n+1) = \sum_{j<n} M(j)\,M(n-1-j)$.

- [Pair partition](is-pair-partition.md)
- [Noncrossing perfect matching](is-ncmatching.md)
- [Noncrossing perfect matchings on $n$ points](ncmatching.md)
- [Splitting off the first arc](split-equiv.md)
- [Catalan recursion for noncrossing matchings](card-nc-matching-succ.md)
- [Counting noncrossing perfect matchings](card-nc-matching.md)
- [Partner map of a pair partition](pair-partner.md)
- [The pair partition of a matching](matching-partition.md)
- [Noncrossing pair partitions are noncrossing perfect matchings](pair-partition-equiv-ncmatching.md)
- [Noncrossing pair partitions of $2k$ points are counted by the Catalan number $C_k$](card-noncrossing-pair-partition-two-mul.md)
- [No noncrossing pair partition of an odd number of points](card-noncrossing-pair-partition-odd.md)
- [Counting noncrossing pair partitions](card-noncrossing-pair-partition.md)

## Related topics

- [Noncrossing partitions and the refinement order](../noncrossing-partitions-and-the-refinement-order/README.md)
- [Catalan numbers](../../../catalan-numbers-lattice-paths/catalan-numbers/catalan-numbers/README.md)
- [Dyck paths and lattice walks](../../../catalan-numbers-lattice-paths/dyck-paths-lattice-walks/README.md)
- [Wigner's semicircle law](../../../../Probability/high-dimensional-probability/wigner-s-semicircle-law/README.md)
