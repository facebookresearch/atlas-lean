# A $9k-8$ kernel for the TBR distance

**Setting.** Let $T, T'$ be unrooted binary phylogenetic trees on a leaf set $X$. A tree bisection and reconnection (TBR) move deletes an edge and reconnects the two resulting subtrees by a new edge between (subdivisions of) any of their edges; $d_{\mathrm{TBR}}(T,T')$ is the minimum number of TBR moves turning $T$ into $T'$. An agreement forest is a partition of $X$ whose blocks induce vertex-disjoint subtrees in both $T$ and $T'$ with matching topologies; a maximum agreement forest (MAF) has the fewest blocks, $d_{\mathrm{MAF}}$, and $d_{\mathrm{TBR}}(T,T') = d_{\mathrm{MAF}}(T,T') - 1$. Computing $d_{\mathrm{TBR}}$ is NP-hard.

**Theorem.** There is a set of ten polynomial-time reduction rules (the classical subtree and chain reductions, three parameter-reducing rules that delete a leaf known to be a singleton in some MAF, and three new rules) such that, if $T$ and $T'$ are irreducible under all of them and $d_{\mathrm{TBR}}(T,T') \ge 2$, then

$$|X| \le 9\,d_{\mathrm{TBR}}(T,T') - 8.$$

Each rule preserves $d_{\mathrm{TBR}}$ or lowers it by exactly one together with the removal of one leaf, so exhaustive application yields a kernel with at most $9k - 8$ leaves for the decision problem "$d_{\mathrm{TBR}}(T,T') \le k$?", and the same kernel applies to unrooted MAF. The bound is tight up to an additive term; earlier kernels had sizes $15k - 9$ and $11k - 9$.

## Expansion

The analysis uses the equivalence $d_{\mathrm{TBR}}(T,T') = k$ if and only if some unrooted phylogenetic network of reticulation number $k$ displays both trees. Such a network is obtained from a cubic generator with $3(k-1)$ sides by hanging taxa on sides, so bounding the number of taxa per side bounds $|X|$. Common chains are preserved by some maximum agreement forest (chain preservation theorem), which caps the length of chains a side can carry. The new rules topologically rearrange both trees without changing the distance so that earlier rules fire, and extend local leaf-deletion arguments to more global configurations, cutting the average number of taxa per generator side to three.

## Sources

- Steven Kelk, Simone Linz and Ruben Meuwese, "Deep kernelization for the Tree Bisection and Reconnection (TBR) distance in phylogenetics", Journal of Computer and System Sciences 142 (2024), 103519, <https://doi.org/10.1016/j.jcss.2024.103519>; numbering as in arXiv:2206.04451: main theorem of Section 3.
