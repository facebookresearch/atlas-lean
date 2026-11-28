# A $9k-8$ kernel for the TBR distance

**Setting.** Let $T, T'$ be unrooted binary phylogenetic trees on a leaf set $X$. A tree bisection and reconnection (TBR) move deletes an edge and reconnects the two resulting subtrees by a new edge between (subdivisions of) any of their edges; $d_{\mathrm{TBR}}(T,T')$ is the minimum number of TBR moves turning $T$ into $T'$. An agreement forest is a partition of $X$ whose blocks induce vertex-disjoint subtrees in both $T$ and $T'$ with matching topologies; a maximum agreement forest (MAF) has the fewest blocks, $d_{\mathrm{MAF}}$, and $d_{\mathrm{TBR}}(T,T') = d_{\mathrm{MAF}}(T,T') - 1$. Computing $d_{\mathrm{TBR}}$ is NP-hard.

**Theorem.** There are ten polynomial-time reduction rules, Reductions 1–10: subtree reduction (1) and chain reduction (2); Reductions 3–7, of which 3 deletes a common 3-chain and 4 and 5 delete a leaf known to be a singleton in some MAF, while 6 and 7 truncate short common chains; and the new Reductions 8–10, of which 8 and 9 rearrange both trees without changing $d_{\mathrm{TBR}}$ and 10 deletes a leaf that is a singleton in some MAF. If $T$ and $T'$ are irreducible under all of them and $d_{\mathrm{TBR}}(T,T') \ge 2$, then

$$|X| \le 9\,d_{\mathrm{TBR}}(T,T') - 8.$$

Reductions 1, 2 and 6–9 preserve $d_{\mathrm{TBR}}$, and Reductions 3, 4, 5 and 10 lower it by exactly one (Reduction 3 by deleting three leaves, the others by deleting one), so exhaustive application yields a kernel with at most $9k - 8$ leaves for the decision problem "$d_{\mathrm{TBR}}(T,T') \le k$?", and the same kernel applies to unrooted MAF. The bound is tight up to an additive term: for each $k\ge3$ there are irreducible trees with $9k-9$ taxa and $d_{\mathrm{TBR}}=k$; earlier kernels had sizes $15k - 9$ and $11k - 9$.

## Depends on

- [Tbr Dist](../../../not-yet-classified/tbragreement-forest/tbr-dist.md)
- [TBR distance equals the maximum agreement forest number](../../../not-yet-classified/tbragreement-forest/tbr-dist-eq-maf-number.md)

## Expansion

The analysis uses the equivalence $d_{\mathrm{TBR}}(T,T') = k$ if and only if some unrooted phylogenetic network of reticulation number $k$ displays both trees. Such a network is obtained from a cubic generator with $3(k-1)$ sides by hanging taxa on sides, so bounding the number of taxa per side bounds $|X|$. Common chains are preserved by some maximum agreement forest (chain preservation theorem), which caps the length of chains a side can carry. The new rules topologically rearrange both trees without changing the distance so that earlier rules fire, and extend local leaf-deletion arguments to more global configurations, cutting the average number of taxa per generator side to three.

## Sources

- Steven Kelk, Simone Linz and Ruben Meuwese, "Deep kernelization for the Tree Bisection and Reconnection (TBR) distance in phylogenetics", Journal of Computer and System Sciences 142 (2024), 103519, <https://doi.org/10.1016/j.jcss.2024.103519>; numbering as in arXiv:2206.04451: Reductions 1–10, Lemma 1, Theorems 7 and 9, the main result Theorem 6 (Section 4) and the tightness result Theorem 15.
