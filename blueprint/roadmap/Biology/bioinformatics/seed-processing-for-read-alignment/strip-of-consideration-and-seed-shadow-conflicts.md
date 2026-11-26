# Strip of consideration and seed shadow conflicts

**Strip of consideration (SoC).** Let $s_M$ be the match score and $p_O, p_E$ the gap open and extension penalties of an affine scoring scheme, and $|Q|$ the query length. The SoC width is

$$\lambda = \frac{s_M |Q| - p_O}{p_E}.$$

For a seed $(q, r, l)$ let $\delta = r - q$ be its diagonal. Two seeds are **spatially local** if $|\delta - \delta'| \le \lambda$; beyond this diagonal distance the gap penalty between them would exceed the best possible match score of the whole query. After sorting seeds by $\delta$, a two-pointer line sweep over windows of diagonal width $\lambda$ scores each window by the total seed length and keeps the non-overlapping best-scoring strips in a priority queue; the cost is dominated by the sort.

**Shadows.** In the plane of reference $\times$ query coordinates, a seed $s = (q, r, l)$ casts the second- and fourth-quadrant shadows

$$\sigma_{II} = [0, r + l] \times [q, |Q|], \qquad \sigma_{IV} = [r, |R|] \times [0, q + l].$$

A seed lying entirely in a shadow of $s$ cannot appear together with $s$ in any alignment, since the two are not in the same order on query and reference. For seeds $s = (q, r, l)$ and $s' = (q', r', l')$:

- $s'$ lies in $\sigma_{II}(s)$ if and only if $q \le q'$ and $r' + l' \le r + l$;
- $s'$ lies in $\sigma_{IV}(s)$ if and only if $r \le r'$ and $q' + l' \le q + l$;

and $s, s'$ **conflict** if and only if one of these holds. Both are interval-in-interval inclusion tests, decided for all pairs of a strip by a line sweep over seeds sorted by query start that compares the order of reference end points. Seed harmonization removes, from each conflicting pair, the seed farther from a robustly fitted diagonal guideline (RANSAC over seed start, center and end points), in $O(|S| \xi + |S|)$ time for $|S|$ seeds where $\xi \le |S|$ bounds the number of conflicts of a single seed.

## Depends on

- [Maximally spanning seeds and binary seeding](maximally-spanning-seeds-and-binary-seeding.md)

## Expansion

An alignment of $Q$ scores at most $s_M |Q|$, and a gap that shifts the diagonal by $g$ costs $p_O + g\, p_E$, so a shift larger than $\lambda$ cannot belong to a positive-scoring alignment; this is the derivation of the width. Unlike chaining, which grows chains seed by seed, the strip selects a candidate region by a linear scan and harmonization purges inconsistent seeds within it, after which banded affine-gap dynamic programming fills the gaps between the surviving seeds. Partial shadowing is allowed: overlapping but correctly ordered seeds remain consistent.

## Sources

- M. Schmidt, K. Heese, A. Kutzner, "Accurate high throughput alignment via line sweep-based seed processing", Nature Communications 10 (2019) 1939, Methods (seeding, Corollaries 1-2, strip of consideration, Equations 1-3, seed harmonization), <https://doi.org/10.1038/s41467-019-09977-2> (PMC6486643).
