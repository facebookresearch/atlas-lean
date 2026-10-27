---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.LeonardoPWanted.hSeqBackward
---

# H Seq Backward

Backward evaluation of the `H(p)` recurrence:
`hSeqBackward seedA p n` is the list of values at
`-p-n, …, p`, starting from the seeds on `[-p, p]` and
prepending one value per step via
`H(t) = H(t+2p) + H(t+p+1) - H(t+2p+1)`.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.LeonardoPWanted](../../../../../../sources/v2/WantedExt.md)
