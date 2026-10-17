---
article_id: af_1f8faed5bbea0cec8ae45274
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.BartleGravesWanted.bartle_graves
---

# Bartle Graves

A surjective operator `T : E →L[ℝ] F` between real Banach spaces admits a continuous (generally
nonlinear) right inverse `g : F → E` with `T (g y) = y`, `g 0 = 0`, positively homogeneous `g (t •
y) = t • g y` for `t ≥ 0`, and bounded `‖g y‖ ≤ C * ‖y‖` for some `C ≥ 0`. Source:
R. G. Bartle and L. M. Graves, Mappings between function spaces,
Trans. Amer. Math. Soc. 72 (1952), 400–413, DOI 10.1090/S0002-9947-1952-0047910-X;
Michael selection theorem precursor; Lean states real Banach case with continuous right
inverse, positive homogeneity, and linear growth bound.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.BartleGraves](../../../../../../sources/v2/MathlibExt.md)
