---
article_id: af_86c20276033b9e07f3127a2e
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.setKey
---

# Set Key

Sort key encoding the paper's set order as one natural number:
`(n - |A|) * 2^n + b(A)`. Since `b(A) < 2^n`, numeric key order agrees with
the paper's set order.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Bin Rep](bin-rep.md)

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.UnionClosedOrderly](../../../../../../../sources/v2/MathlibExt.md)
