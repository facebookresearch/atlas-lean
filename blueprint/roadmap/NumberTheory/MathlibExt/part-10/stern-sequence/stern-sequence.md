---
article_id: af_b64566b02907561112e90e0d
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.sternSequence
---

# Stern Sequence

Stern sequence (`jis_term_8e87f9eebae5b6160acdc06a`, "Stern diatomic sequence",
OEIS A002487): the function `s : Nat → Nat` with `s 0 = 0`, `s 1 = 1`,
`s (2 * n) = s n` and `s (2 * n + 1) = s n + s (n + 1)` for `n ≥ 1`
(JIS Lansing, lines 92-103; JIS Dennison, lines 80-85).

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.SternSequence](../../../../../sources/v2/MathlibExt.md)
