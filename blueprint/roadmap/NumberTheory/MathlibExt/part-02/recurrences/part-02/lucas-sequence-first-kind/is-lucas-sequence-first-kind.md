---
article_id: af_e6f96479a0157b7d5b9a28be
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsLucasSequenceFirstKind
---

# Is Lucas Sequence First Kind

`IsLucasSequenceFirstKind P Q u` holds exactly when `u` satisfies the
Lucas sequence of the first kind recurrence with parameters `P Q`:
`u 0 = 0`, `u 1 = 1`, and `u (n + 2) = P * u (n + 1) - Q * u n` for all `n`.

Provenance: stable record `jis_grounded_7e37bcd48e7477bda602ca6e`,
`https://cs.uwaterloo.ca/journals/JIS/VOL13/Smyth/smyth2.tex`,
lines 114-122.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Recurrences.LucasSequenceFirstKind](../../../../../../../sources/v2/MathlibExt.md)
