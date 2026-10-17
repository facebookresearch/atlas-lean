---
article_id: af_663b1e9261be98e6fceabe79
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MetaMathlibExt.viviani
---

# Viviani

Viviani's theorem, source-shaped form (statement `viviani-s1`): thin
wrapper over `viviani_general` retaining the frozen Wanted signature,
including its (unused) positivity hypothesis `0 < dist A B`, for exact
compatibility with the former `Wanted` entry. New callers should prefer
`viviani_general`, which needs no positivity hypothesis.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Viviani general](viviani-general.md)

## Sources

- [MathlibExt, MathlibExt.Geometry.Euclidean.Viviani](../../../../../../sources/v2/MathlibExt.md)
