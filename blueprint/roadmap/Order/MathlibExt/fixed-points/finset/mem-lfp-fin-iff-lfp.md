---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Finset.mem_lfpFin_iff_lfp
---

# Mem lfp Fin iff lfp

Convergence for least fixed points: under the bridge hypothesis,
`lfpFin f` computes the least fixed point of `F`.  One inclusion is
iteration into the fixed point; the other is Park induction, where the
`Fintype.card α`-th `F`-iterate is pre-fixed because the
corresponding `f`-iterate has stabilized (`lfpFin_fixed`), transported
across the bridge.

## Depends on

- [Lfp Fin](lfp-fin.md)

## Proof depends on

- [Lfp Fin fixed](lfp-fin-fixed.md)
- [Mem finset iterate iff](mem-finset-iterate-iff.md)

## Sources

- [MathlibExt, MathlibExt.Order.FixedPoints.Finset](../../../../../sources/v2/MathlibExt.md)
