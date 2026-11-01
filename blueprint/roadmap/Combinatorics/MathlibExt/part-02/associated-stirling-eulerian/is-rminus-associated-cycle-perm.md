---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsRMinusAssociatedCyclePerm
---

# Is RMinus Associated Cycle Perm

An `r`-minus-cycle permutation of `Fin n`: every cycle length is at most `r`.

Fixed one-cycles are omitted by `Equiv.Perm.cycleType`, so they are handled
explicitly: a fixed point requires `1 ≤ r`, and every nontrivial entry of
`σ.cycleType` requires `≤ r`. The point condition is vacuous for `Fin 0`.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 106-108 and Lines 257-259;
URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.AssociatedStirlingEulerian](../../../../../sources/v2/MathlibExt.md)
