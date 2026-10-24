---
article_id: af_f679ecc91cb07abf3e1f69b3
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.Complex.KoebeQuarterWanted.koebe_quarter
---

# Koebe Quarter

If `f : ℂ → ℂ` is holomorphic and injective on `ball (0:ℂ) 1` with `f 0 = 0` and `deriv f 0 = 1`,
then `ball (0:ℂ) (1/4 : ℝ) ⊆ f '' ball (0:ℂ) 1`. Source: Koebe quarter theorem, conjectured by
P. Koebe in 1907 and proved by L. Bieberbach, Sitzungsberichte der Preussischen Akademie der
Wissenschaften (1916), 940–955; see Pommerenke, Univalent Functions; Lean is normalized schlicht
inclusion ball (0:ℂ) (1/4) ⊆ f '' ball 0 1.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.Complex.KoebeQuarter](../../../../../../sources/v2/MathlibExt.md)
