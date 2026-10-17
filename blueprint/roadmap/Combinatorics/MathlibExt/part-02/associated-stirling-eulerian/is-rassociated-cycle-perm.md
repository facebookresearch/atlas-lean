---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.IsRAssociatedCyclePerm
---

# Is RAssociated Cycle Perm

An `r`-associated-cycle permutation of `Fin n`: every cycle length exceeds `r`.

Fixed one-cycles are omitted by `Equiv.Perm.cycleType`, so they are handled
explicitly: a fixed point requires `r < 1`, and every nontrivial entry of
`σ.cycleType` requires `r <` its length. The point condition is vacuous for
`Fin 0`, including when `r = 0`.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 106-108 and Lines 653-657;
URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.AssociatedStirlingEulerian](../../../../../sources/v2/MathlibExt.md)
