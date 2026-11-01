---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.genLeonardo
---

# Gen Leonardo

The generalized Leonardo numbers `L_{k,n}`: `L_{k,0} = L_{k,1} = 1` and
`L_{k,n+2} = L_{k,n+1} + L_{k,n} + k`. The paper fixes `k` positive; the
recurrence here is stated over `ℤ` (an intentional domain extension,
bridged to the existing `p = 1` API by
`genLeonardo_eq_leonardoPK_one` below).

## Depends on

This node has no prerequisites.

## Sources

- [WantedExt, WantedExt.NumberTheory.GenLeonardoWanted](../../../../../sources/v2/WantedExt.md)
- Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly 62.3 (2024), introduction.
