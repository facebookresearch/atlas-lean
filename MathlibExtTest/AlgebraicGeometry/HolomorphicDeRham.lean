/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.HolomorphicDeRham

@[expose] public section

/-!
# Tests for the holomorphic de Rham interface

Chart coefficients of forms are additive and homogeneous, and the zero form
has zero coefficients, so holomorphic forms form a subspace. The rational and
complex unit complexes are the constant sheaves concentrated in degree zero:
their degree-zero term is the constant sheaf and every other term is zero.
-/

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open MathlibExt.AlgebraicGeometry
open MathlibExt.AlgebraicGeometry.AnalyticRealization
open MathlibExt.AlgebraicGeometry.HolomorphicDeRham

namespace MathlibExtTest.AlgebraicGeometry.HolomorphicDeRham

variable (X : ComplexScheme) (d : ℕ) [AnalyticManifold X d]
  {U : Opens (ComplexAnalytification.space X)} {p : ℕ}

example (a : ComplexAnalytification.space X) (σ : Fin p → Fin d) :
    chartCoefficient X d (0 : RoughForm X d U p) a σ = 0 := by
  simp

example (α β : RoughForm X d U p) (c : ℂ) (a : ComplexAnalytification.space X)
    (σ : Fin p → Fin d) :
    chartCoefficient X d (c • α + β) a σ =
      c • chartCoefficient X d α a σ + chartCoefficient X d β a σ := by
  rw [chartCoefficient_add, chartCoefficient_smul]

/-- Sums and scalar multiples of holomorphic forms are holomorphic. -/
example (α β : holomorphicForms X d U p) (c : ℂ) :
    IsHolomorphicForm X d ((c • α + β : holomorphicForms X d U p) : RoughForm X d U p) :=
  (c • α + β).2

example : (rationalRestriction X).Additive := inferInstance

/-- The rational unit complex is the constant sheaf in degree zero. -/
example : (rationalUnitComplex X).X 0 ≅
    (constantSheaf (Opens.grothendieckTopology (ComplexAnalytification.space X))
      (ModuleCat.{0} ℚ)).obj (ModuleCat.of ℚ ℚ) :=
  HomologicalComplex.singleObjXSelf _ _ _

example (j : ℤ) (hj : j ≠ 0) : IsZero ((rationalUnitComplex X).X j) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hj

example (j : ℤ) (hj : j ≠ 0) : IsZero ((complexUnitComplex X).X j) :=
  HomologicalComplex.isZero_single_obj_X _ _ _ _ hj

/-- A brutal cut vanishes below its degree and agrees with the complex from
its degree on. -/
example (D : HolomorphicDeRhamData X d) (q : ℤ) (H : HodgeCut D q) (j : ℤ) (hj : q ≤ j) :
    IsIso (H.inclusion.f j) :=
  H.unchanged_above j hj

end MathlibExtTest.AlgebraicGeometry.HolomorphicDeRham
