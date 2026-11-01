---
article_id: af_d9dab132136ae88c704113eb
declaration: def
origin: cited
statement: formalized
lean: BooleanCube.multilinearExtension
---

# Multilinear Extension

The real multilinear extension of a Boolean function. For each cube point
`x`, the product is its Lagrange indicator: it is one at `x` and zero at every
other Boolean point. The sum is therefore the unique multilinear polynomial
agreeing with `f` on `{0,1}^n`.

## Depends on

- [Bool Cube](bool-cube.md)

## Proof depends on

- [Cube Basis](cube-basis.md)

## Sources

- [MathlibExt, MathlibExt.Analysis.Fourier.BooleanCube](../../../../../../../sources/v2/MathlibExt.md)
