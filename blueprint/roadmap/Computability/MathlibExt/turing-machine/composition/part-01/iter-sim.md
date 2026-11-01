---
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.TM2Composition.iter_sim
---

# Iter sim

A step-respecting embedding transports runs. Halted configurations are absorbing, so every
intermediate configuration of a run that ends in `some d` is live.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Iter none](../../program/part-01/iter-none.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Composition](../../../../../../sources/v2/MathlibExt.md)
