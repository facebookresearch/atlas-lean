---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.TM2Composition.compTime
---

# Comp Time

Time bound of the composite machine: `p₁ + 4·(X + c·p₁) + 2 + p₂ ∘ (X + c·p₁)`
(two copy loops of `2m + 1` steps each, with `m ≤ n + c·p₁(n)`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Mid Poly](mid-poly.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Composition](../../../../../../sources/v2/MathlibExt.md)
