# Maximally spanning seeds and binary seeding

**Setting.** A seed is a triple $(q, r, l)$ stating that the query $Q$ on $[q, q + l)$ equals the reference $R$ on $[r, r + l)$. A full-text index (such as an FMD-index) supports, in $O(1)$ each, backward and forward extension of an implicit occurrence set by one character. For a seed set $S$ let $S.\mathrm{begin} = \min\{q\}$ and $S.\mathrm{end} = \max\{q + l\}$ over its seeds.

- $S$ is **fully covering** if every query position $0 \le i < |Q|$ lies in some seed of $S$ (possible only if the query alphabet is contained in the reference alphabet).
- A seed is **non-enclosed** in $S$ if no other seed $(q', r', l')$ of $S$ has $q' \le q < q + l \le q' + l'$.
- $S$ is **maximally spanning** with respect to $i$ if every seed of $S$ covers $i$ and no seed covering $i$ starts before $S.\mathrm{begin}$ or ends after $S.\mathrm{end}$.

**Procedure.** From position $i$, extend maximally backwards and then maximally forwards, giving a seed set with a common query interval; repeat in the opposite order; return the union.

**Corollary 1.** Let $S'$ be the set of all seeds that span query position $i$ ($0 \le q' \le i < q' + l' \le |Q|$) and $S$ the output of the procedure. No seed of $S'$ has $q' < S.\mathrm{begin}$ or $q' + l' > S.\mathrm{end}$; that is, $S$ is maximally spanning for $i$.

**Binary seeding.** Starting from the whole query interval $[b, e)$, compute the maximally spanning seeds at the midpoint $\lfloor (b + e)/2 \rfloor$, which cover $[S.\mathrm{begin}, S.\mathrm{end})$, and recurse on the non-empty left and right remainders $[b, S.\mathrm{begin})$ and $[S.\mathrm{end}, e)$. The result is a fully covering seed set.

**Corollary 2.** Binary seeding terminates for every query $Q$ and reference index.

Maximally spanning seeds form a subset of the supermaximal exact matches (non-enclosed seeds); the omitted non-enclosed seeds are those completely covered by two or more longer non-enclosed seeds, which cannot be part of an optimal alignment.

## Depends on

- [FM-index backward search](../../../../ComputerScience/string-algorithms/burrows-wheeler-transform-and-fm-index/backward-search.md)

## Expansion

Corollary 1 follows because a maximal extension stops only when the next character yields no occurrence, so a seed through $i$ reaching further left (or right) would contradict maximality of the backward (forward) phase. For Corollary 2, every seed returned at the midpoint $p$ has length at least $1$ and contains $p$, so $S.\mathrm{begin} \le p < S.\mathrm{end}$; the two remainders therefore have total length strictly less than $e - b$, and the recursion depth is bounded by the query length.

## Sources

- M. Schmidt, K. Heese, A. Kutzner, "Accurate high throughput alignment via line sweep-based seed processing", Nature Communications 10 (2019) 1939, Methods (seeding, Corollaries 1-2, strip of consideration, Equations 1-3, seed harmonization), <https://doi.org/10.1038/s41467-019-09977-2> (PMC6486643).
