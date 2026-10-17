---
article_id: af_68867e1a71cb30b558129162
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Matching.GaleShapley.gale_shapley_exists_stable_matching
---

# Gale shapley exists stable matching

For two finite equal-cardinality sides with strict total preferences over opposite side, a stable
perfect matching exists.

## Depends on

- [Is Stable](is-stable.md)
- [MPrefs](mprefs.md)
- [Perfect Matching](perfect-matching.md)
- [WPrefs](wprefs.md)

## Proof depends on

- [Gale shapley exists stable matching general](gale-shapley-exists-stable-matching-gene.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Matching.GaleShapley](../../../../../../sources/v2/MathlibExt.md)
- D. Gale and L. S. Shapley, "College Admissions and the Stability of Marriage", American Mathematical Monthly 69 (1962), 9–15, DOI 10.2307/2312726. It follows from `gale_shapley_exists_stable_matching_general`; the instances `[DecidableEq M]` and `[DecidableEq W]` are unused and keep the source's shape. Proves `Wanted` entry `gale_shapley_exists_stable_matching`.
