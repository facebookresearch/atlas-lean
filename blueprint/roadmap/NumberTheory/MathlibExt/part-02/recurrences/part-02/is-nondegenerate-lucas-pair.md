---
article_id: af_3cedc0b0ebfd3a2ff9a5cbde
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsNondegenerateLucasPair
---

# Nondegenerate Lucas Pair

Nondegeneracy predicate for Lucas pairs.

Grounded in the frozen source
`https://cs.uwaterloo.ca/journals/JIS/VOL13/Smyth/smyth2.tex`
(file SHA-256 `eb765815f14b18e047ccd51b0ed4ec17305d9410f60516b290425a6cd7a49d05`):
exact lines 621-622, bytes 31221-31556,
span SHA-256 `146ace40668919cc30347d312b9fa8a392a3ba872d0eef5fc1e79c36f6d27cd8`,
say a Lucas sequence is degenerate iff `Q = 0` or `α / β` is a root of unity,
where `α` and `β` are the two roots of `x² - P x + Q`.
Supporting lines 114-122, bytes 3175-3840,
SHA-256 `dce48c9908ba3e56bb82b2792cbb734d489dc1558763f1c1284855dc2de7ea4f`,
establish `α + β = P` and `α * β = Q`.

This predicate requires `Q ≠ 0` and requires `α / β` not to be of finite order
for every complete complex root pair satisfying both `α + β = (P : ℂ)` and
`α * β = (Q : ℂ)`.

Stable record: `jis_grounded_7e37bcd48e7477bda602ca6e`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.NondegenerateLucasPair](../../../../../../sources/v2/MathlibExt.md)
