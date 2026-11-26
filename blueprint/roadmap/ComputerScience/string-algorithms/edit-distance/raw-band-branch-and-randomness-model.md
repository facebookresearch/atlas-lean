# Branch guard and product law of raw-band edit approximation

This is the fixed computation specified by the linked declarations, not a quantifier over randomized algorithms. For integer inputs use the injective coding $z\mapsto2z$ for $z\ge0$ and $-n-1\mapsto2n+1$. The binary accuracy is a signed little-endian numerator and a positive little-endian denominator. Let $h=\lceil\log_2\lceil\log_2(N+2)\rceil\rceil$, $H=2^h$, $u=\lceil\log_2\max(1,h)\rceil$ and $\ell=2^u$, using the natural ceiling log. Put $p=\lfloor\sqrt{\lfloor\sqrt{\lfloor\log_2\ell\rfloor}\rfloor}\rfloor$, $M=2^{\lfloor h/20\rfloor}$, $P=H^{p+20}$ and $B=H^p$. The large branch is used exactly when both accuracy words have length at most $H$, $\ell\ge2^{1000}$, $\ell\varepsilon\ge10$, and the binary digit count (`Nat.size`) of $\sum_{j=1}^K j$ is at most $H$, where $K=(H+M(40P+2)^2+2)^{80}$. If false, the law is the point mass on the fallback tag. The fallback computes the exact suffix edit distance on the encoded lists.

On the large branch the law is the product of the coarse seed law and the rejection-runtime law, tagged as the large outcome. A depth-zero coarse draw is a single point. At depth $d+1$ it consists of $B$ independent uniform indices in $\{0,\ldots,B-1\}$ and $B$ independent recursively distributed depth-$d$ draws. For each physical source-tree/target-interval entry take $m$ to be the maximum of the source subword and target interval lengths. The threshold guesses are $2^j$ for natural $0\le j\le\lceil\log_2 m\rceil$, and each gets an independent draw at depth $\lceil\log_{B}\max(1,m)\rceil$ (using the source's `Nat.clog`, including at degenerate bases or widths). The pinned `PhysicalEntry`, `computedPhysicalCoarseDepth` and `CoarseGuessIndex` specify the exact index set and convention. Project these coarse draws to the clamped seed table using `physicalCoarseSeedTable` (an indexed initial upper-estimate table, not an extra independent draw).

The other component has one independent pair per bounded physical scalar-family key: a count of rejected draws and a uniform accepted value in $\{0,\ldots,r-1\}$. For a range $r>0$, rejection draws from $\{0,\ldots,2^{\lceil\log_2 r\rceil}-1\}$, so the count of failures before success has geometric parameter $r/2^{\lceil\log_2 r\rceil}$ and the accepted value is independent of that count. The range for an online key is its stored range and for a nonlocal key is $M$. The family uses the source’s typed `PhysicalFamilyScalarKey` (pass, copy, and scalar address), with $F=\ell$, band exponent $40u$, scale cap $\ell^{80}$, refinement and copy bounds $H^2$, and the exact pass count `computedSeedPassCount N`. The query input is the pair of the projected coarse table and this accepted-value array; the rejection counts are kept for cost, not supplied as values to the memoized answer. The links below fix the detailed indexing definitions rather than permitting another enumeration, projection or distribution.

## Depends on

- [Unit-cost edit distance used by the suffix fallback](edit-distance.md)
- The natural bit-count conventions and source-defined finite product and geometric measures.

## Expansion

Represent the bounded key family and its measures at the same indices before connecting to a native randomized machine. Establish that the projection and large-branch decision preserve the displayed law; do not replace rejection effort by expected effort pointwise.

## Sources

- [Exact bounded prefix inspection](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L257-L271)
- [Binary accuracy inspection](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L576-L583)
- [Integer parameters and coarse thresholds](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L638-L649)
- [Height and coarse exponent](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L67-L76)
- [Dyadic logarithm exponent](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L363)
- [Power-of-two small-log parameter](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L529)
- [Large accuracy test](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L673-L684)
- [Online mass bound](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L1797-L1806)
- [Binary branch-guard procedure with work](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L5027-L5079)
- [Recursive uniform coarse law](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L5501-L5535)
- [Threshold guesses and coarse seed distribution](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L8094-L8143)
- [Entry depth and scalar ranges](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L12921-L12957)
- [Rejection runtime and accepted laws](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L14896-L14963)
- [Computed coarse/rejection product and branch guard](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L14971-L15066)
- [Full law and accepted projection](https://github.com/openai/math/blob/3344da59991ed94f9ba711217b29c1d760badfa6/lean/ComparatorChallenges/EditApproximation.lean#L15155-L15205)
