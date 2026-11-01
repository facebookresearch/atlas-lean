---
declaration: def
origin: cited
statement: formalized
lean: Cslib.Algorithms.Lean.Matrix.freivaldsTrial
---

# Freivalds Trial

Compute and materialize `B r`, `A (B r)`, and `C r`, then compare the two
result columns. The input coefficient domain is `ZMod 2` by intentional specialization (see the
module note), not by a restriction in the cited source.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Rectangular Matrix Accumulate](../../multiply/rectangular-matrix-accumulate.md)

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.Matrix.Freivalds.Basic](../../../../../../../sources/v2/CSLibExt.md)
