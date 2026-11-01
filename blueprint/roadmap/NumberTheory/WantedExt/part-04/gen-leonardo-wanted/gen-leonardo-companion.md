---
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.genLeonardoCompanion
---

# Gen Leonardo Companion

The dual generalized Leonardo numbers `M_{k,n}`: the paper's
Definition 2.1 gives `M_{k,0} = 1 - k`, `M_{k,1} = k + 3`, and
`M_{k,n+1} = M_{k,n} + M_{k,n-1} + 2k` for `n ≥ 1`; the paper's
identity (2.1) gives `M_{k,n} = L_{k,n-1} + L_{k,n+1}`. The
closed form used here agrees with Definition 2.1 on all `n` and
with the paper's value table (checked for `k = 1` to `n = 14`).

## Depends on

This node has no prerequisites.

## Proof depends on

- [Gen Leonardo](gen-leonardo.md)

## Sources

- [WantedExt, WantedExt.NumberTheory.GenLeonardoWanted](../../../../../sources/v2/WantedExt.md)
- Kuhapatanakul, *Note on the Generalized Leonardo Numbers*, Fibonacci Quarterly 62.3 (2024), Definition 2.1 and identity (2.1).
