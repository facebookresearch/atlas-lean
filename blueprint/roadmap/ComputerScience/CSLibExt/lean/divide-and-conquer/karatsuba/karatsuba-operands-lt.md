---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: Cslib.Algorithms.Lean.TimeM.karatsuba_operands_lt
---

# Karatsuba operands lt

For an input below `B^n`, its high part, low part and their difference are below `B^⌈n/2⌉`.
Applied to both inputs, all six recursive operands stay within the digit model, and the base case
multiplies single digits.

## Depends on

This node has no prerequisites.

## Sources

- [CSLibExt, CSLibExt.Algorithms.Lean.DivideAndConquer.Karatsuba](../../../../../../sources/v2/CSLibExt.md)
