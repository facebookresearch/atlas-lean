---
article_id: af_05f957069e78649c94773ff8
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.BrowderKirkWanted.browderGoehdeKirk_fixedPoint
---

# Browder Kirk

In a complete uniformly convex real normed space, every nonexpansive self-map `f : E → E` with
`MapsTo f K K` and `LipschitzOnWith 1 f K` of a nonempty closed bounded convex set `K` has a fixed
point in `K`, i.e. `∃ y ∈ K, f y = y`. Source: F. Browder, Proc. Nat. Acad. Sci. USA 1965, D.
Göhde, Math. Ann. 1965, and W. Kirk, Amer. Math. Monthly 1965-66, fixed-point theorem for
nonexpansive mappings in uniformly convex Banach spaces; textbook Goebel and Kirk, 1990; Lean
states complete uniformly convex real case with `Bornology.IsBounded` convex set.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.BrowderKirk](../../../../../../sources/v2/MathlibExt.md)
