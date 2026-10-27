---
article_id: af_e480f5009dcddad3e6f107be
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.InnerProductSpace.KirszbraunWanted.kirszbraun_general
---

# Kirszbraun general

For a real inner-product space `E` (not necessarily complete) and a complete real inner-product
space `F`, every `K`-Lipschitz map `f : E → F` on a set `s` extends to a globally `K`-Lipschitz
map `g : E → F` with `EqOn f g s` and the same constant `K`. Source: M. Kirszbraun, Fund. Math.
22 (1934) 77-108 thesis; Valentine 1945 extension to Hilbert; Federer, Geometric Measure Theory,
2.10.43; the Lean theorem takes a real inner-product-space domain `E` and a complete real
inner-product-space target `F`, with the same Lipschitz constant `LipschitzWith K`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.InnerProductSpace.Kirszbraun](../../../../../../sources/v2/MathlibExt.md)
