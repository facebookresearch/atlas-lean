---
article_id: af_4ce83c17b2a15c71b3b86814
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Combinatorics.Additive.SarkozyWanted.furstenberg_sarkozy
---

# Furstenberg sarkozy

If `A ⊆ ℕ` has positive upper density, witnessed by `δ > 0` with `δ * N ≤ |A ∩ range N|` for
arbitrarily large `N`, then there are `a, b, k ∈ ℕ` with `a ∈ A`, `b ∈ A`, `0 < k`, `a < b`, and
`b = a + k * k`. Source: A. Sárközy, Acta Math. Acad. Sci. Hungar. 31 (1978) and H. Furstenberg,
J. Analyse Math. 31 (1977); Lean states positive upper density via `initialSegmentCount` with
arbitrarily large N.

## Depends on

- [Initial Segment Count](initial-segment-count.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Additive.Sarkozy](../../../../../../sources/v2/MathlibExt.md)
