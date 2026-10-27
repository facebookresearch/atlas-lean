---
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.NumberTheory.LeonardoPWanted.hSeqForward
---

# H Seq Forward

Forward evaluation of the `H(p)` recurrence
`H(n) = H(n-1) + H(n-p) - H(n-2p-1)`: `hSeqForward seedA p n`
is the list of values at `-p, -p+1, …, p+n`, starting from
the seeds `seedA` on `[-p, p]` and appending one value per
step (position `i` holds the value at `i - p`). Evaluation
is polynomial: each step reuses the shared prefix list.

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.LeonardoPWanted](../../../../../../sources/v2/WantedExt.md)
