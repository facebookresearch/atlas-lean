---
article_id: af_919158f2d0c210851e4ec24a
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.invertTransform
---

# Invert Transform

INVERT transform of an integer sequence (concept `jis_sem_22fea8fd5a269c1828606fd8`;
source statements `jis_bdc94f3dcf45a8b11a488c9a`, `jis_fa06f78544747f9465a909ce`,
`jis_a1ec2137c84e5b9b5ce1f3f7`, `jis_dc5074e4bf1c7aedd3a999d3`).
Lean index `n` denotes source index `n+1` for both input and output.
The input ordinary generating function is embedded as `X * mk a`, whose constant
coefficient is zero, and the output is read off degrees `n+1` of the inverse of
`1 - X * mk a` obtained by `invOfUnit` with the unit `1` over `Int`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Combinatorics.Enumerative.InvertTransform](../../../../../../../sources/v2/MathlibExt.md)
