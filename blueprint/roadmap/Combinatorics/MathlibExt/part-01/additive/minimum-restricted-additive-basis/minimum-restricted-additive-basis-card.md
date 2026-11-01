---
article_id: af_8efb257bb2e06b4101d223d1
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.minimumRestrictedAdditiveBasisCard
---

# Minimum Restricted Additive Basis Card

Minimum restricted additive-basis cardinality for `[0, s]`: the summand
set `A : Finset ℕ` satisfies the restriction `2 * a ≤ s` for all `a ∈ A`;
every `x ≤ s` equals `a + b` for some `a ∈ A`, `b ∈ A` (independent choices,
so `a = b` allowed); `A.card = k` for `opt = some k`, minimal among all such
witness sets; `opt = none` exactly when no such witness set exists. The
restriction `2 * a ≤ s` applies for every `s`, odd or even, with no parity
requirement and no sentinel value for absence.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Additive.MinimumRestrictedAdditiveBasis](../../../../../../sources/v2/MathlibExt.md)
- Jukka Kohonen, Visa Koivunen, and Robin Rajamäki, *Planar Additive Bases for Rectangles*, Journal of Integer Sequences 21 (2018), Article 18.9.8: additive-basis notion (`A + A ⊇ [0, n]`), lines 126–128; one-dimensional restricted basis (`A ⊆ [0, n/2]`), lines 170–171; minimum restricted-basis notation `k^*`, lines 200–203, <https://cs.uwaterloo.ca/journals/JIS/VOL21/Rajamaki/raj.tex>. The one-dimensional `k^*(s, 0)` notion supports G. Yu's restricted 2-basis bound (`s_x / k^*(s_x, 0)^2 ≤ 0.41983`, equation `eq:yu_restr`, lines 897–901), quoting G. Yu, *Upper bounds for finite additive 2-bases*, Proc. Amer. Math. Soc. 137 (2009), 11–18, Theorem 1.2.
