---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.TM2Program.Bud
---

# Bud

Budgeted run, for goal-directed chaining: `K` steps are already spent, the run from `c` to
`d` takes `n` more, and `K + n ≤ X`. Chaining lemmas only extend `K`, so every implicit
argument is fixed by first-order unification.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Run](../part-01/run.md)

## Sources

- [MathlibExt, MathlibExt.Computability.TuringMachine.Program](../../../../../../sources/v2/MathlibExt.md)
