---
article_id: af_b4454a7b07604a18435e3c60
declaration: def
origin: cited
statement: formalized
lean: PeriodPair.poleMultiplicity
---

# Pole Multiplicity

Pointwise pole multiplicity of `f` at `z`, defined locally from
`meromorphicOrderAt f z`.

The multiplicity is the negation of the order, truncated to `ℕ`: a pole of order
`-n` contributes `n`, while zeros, nonzero values, and points where `f` is not
locally meromorphic (junk order `0`) contribute `0`. Since only the local order is
used, the value at `z` never depends on the behavior of `f` far away from `z`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.SpecialFunctions.Elliptic.Order](../../../../../../../../sources/v2/MathlibExt.md)
