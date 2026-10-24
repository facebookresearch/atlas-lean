---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Finset.lfpFin_fixed
---

# Lfp Fin fixed

The iterates of a monotone `Finset` functional from `∅` stabilize
within `Fintype.card α` steps: the chain is increasing, and until it
stabilizes each step strictly increases the cardinality, which is
bounded by `Fintype.card α`.

## Depends on

- [Lfp Fin](lfp-fin.md)

## Sources

- [MathlibExt, MathlibExt.Order.FixedPoints.Finset](../../../../../sources/v2/MathlibExt.md)
