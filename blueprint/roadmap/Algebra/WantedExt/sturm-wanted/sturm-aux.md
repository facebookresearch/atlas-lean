---
article_id: af_3b877c9557971607a453df7b
declaration: def
origin: cited
statement: formalized
lean: MathlibExt.Algebra.SturmWanted.Algebra.sturmAux
---

# Sturm Aux

Recursive helper for the Sturm chain. `sturmAux a b n` extends the chain
starting from successive entries `a, b` with fuel `n`: at each step it
appends `a` and continues with `b` and `-(a % b)`, stopping when the next
entry is `0` (or the fuel runs out).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.Algebra.SturmWanted](../../../../sources/v2/WantedExt.md)
