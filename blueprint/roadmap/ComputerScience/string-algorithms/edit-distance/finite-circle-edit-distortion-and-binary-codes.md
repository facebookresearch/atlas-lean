# Finite-circle edit distortion and local binary codes

Use the edit distance, least ℓ₁ distortion and scale $g_b(d)$ in the [uniform distortion estimate](uniform-edit-distance-distortion-scale.md). There exist $c,C,a,C_0,\delta,\eta>0$ and $d_0$ with the following joint properties.

For every finite alphabet $A$ of size at least two there are two fixed-width binary block codes (widths may differ). Each width satisfies $0<w\le C_0\log(2|A|)$. For equal-length words, the deficit (length minus longest common subsequence) after block concatenation lies between $aw$ and $w$ times the input deficit. For arbitrary words the encoded edit distance is at most $w$ times the original. The first code additionally bounds the LCS of any two in-range windows of length $\lfloor w/8\rfloor$ from different symbol blocks by $(1-\delta)\lfloor w/8\rfloor$. The second requires that any matching of increasing position lists of equal length at least $w/4$, having span minus length at most $\eta w$ in each block, uses the same symbol and has a matched position with identical indices.

For all $d\ge d_0$ and all such alphabets there is a finite-coordinate map of the capped words with ℓ₁ distances between $d_E$ and $g_C(d)d_E$, and their least distortion is between $g_c(d)$ and $g_C(d)$. These same bounds apply to the supremum over alphabet sizes. At each such cap there are two equal-positive-length binary image sets with length at most $d$ and distortion at least $g_c(d)$: one is the mask-tag recursion below encoded with the first kind of code, and one is the excluded-prime recursion encoded with the second kind.

In each recursion take depth $h\ge2$, $h^2$ distinct primes $p_{lk}$ grouped by level, $P_l=\prod_k p_{lk}$, $M=2\prod_l P_l$, and repeat the level-$l$ phase index $s=0,\ldots,h^{2h}P_l-1$. Leaf states are residues $v\bmod M$. In the mask case primes lie in $[h^3,2h^3]$. At each phase concatenate children in tag order $(k,b)$, $0\le b<p_{lk}$, prefixing that tag to their symbols and adding the residue $\sum_j (M/p_{lj})(s\bmod p_{lj})+b(M/p_{lk})(s\bmod p_{lk})$ to all descendant states of that child. The leaf emits the half-circle indicator at each residue $x$, testing $(x-v)\bmod M<M/2$. In the excluded-prime case primes lie in $(h^3,h^5]$; concatenate children in order $k$ with prefix $k$ and shift $\sum_{j\ne k}(M/p_{lj})(s\bmod p_{lj})$. Each leaf emits the same indicator but pairs it with its coordinate $x$. The sets range over all assignments of leaf states before coding.

## Depends on

- [Edit distance](edit-distance.md)
- Longest common subsequences; two tagged recursive families and two block-code locality predicates as defined above.

## Proof depends on

- Existence of offset-local and anchor-local codes, distortion for the two recursive finite-circle obstructions, and the uniform finite histogram embedding.

## Expansion

Split the block-code existence, mask obstruction, excluded-prime obstruction, explicit upper embedding, and the common scale corollaries. Preserve the same bound parameters wherever the comparator uses them jointly.

## Sources

- [Comparator statement: `OAI.finiteCircle_fullMain`](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/FiniteCircle.lean#L225-L227)
- [Formalization scope](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/docs/099.md)
