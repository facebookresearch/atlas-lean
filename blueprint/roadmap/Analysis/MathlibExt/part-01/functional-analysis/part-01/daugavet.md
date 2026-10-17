---
article_id: af_619981bdcaed3844207afe3e
declaration: theorem
origin: cited
statement: formalized
proof: formalized
lean: MathlibExt.Analysis.FunctionalAnalysis.DaugavetWanted.daugavet
---

# Daugavet

Every compact operator `T : C([0, 1], ℝ) →L[ℝ] C([0, 1], ℝ)` on `C(Set.Icc 0 1, ℝ)` with the sup
norm satisfies the Daugavet equation `‖id + T‖ = 1 + ‖T‖`. Source: I. K. Daugavet, Izv. Vyssh.
Uchebn. Zaved. Matematika 1963; Kadets et al., 1980s Daugavet property; Werner, Recent progress on
Daugavet property, 2001; Lean states `C(Icc 0 1, ℝ)` compact-operator specialization of the
general Daugavet property `‖Id+T‖=1+‖T‖`.

## Depends on

This node has no prerequisites.

## Sources

- [MathlibExt, MathlibExt.Analysis.FunctionalAnalysis.Daugavet](../../../../../../sources/v2/MathlibExt.md)
