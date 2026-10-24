---
article_id: af_aa6159c8544f73889aaacc54
declaration: def
origin: cited
statement: formalized
lean: MetaMathlibExt.cubicResidueSymbolRaw
---

# Cubic Residue Symbol Raw

Implementation detail: totalizes zero denominators to `0` and ignores
out-of-domain prime factors via the raw factor. Prefer `cubicResidueSymbol`
with `IsCubicResidueDenominator`.

## Depends on

This node has no prerequisites.

## Proof depends on

- [Prime Ideal Cubic Symbol Factor Raw](prime-ideal-cubic-symbol-factor-raw.md)

## Sources

- [MathlibExt, MathlibExt.NumberTheory.Cyclotomic.CubicResidueSymbol](../../../../../../sources/v2/MathlibExt.md)
