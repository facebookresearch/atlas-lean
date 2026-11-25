/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
module

public import Mathlib.AlgebraicTopology.ModelCategory.BrownLemma
public import Mathlib.AlgebraicTopology.ModelCategory.Homotopy

/-!
# Whole endpoint comparison for a genuine fibrant Brown factorization

The trivial-fibration retraction of a Brown factorization gives an actual
homotopy from its retraction-section composite to the identity. The native
homotopy-class injectivity and left/right homotopy bridge produce a whole
good path-object map with endpoints equal to the two original factor maps.
The original map is not assumed weak.
-/

@[expose] public section

noncomputable section
universe u v
open CategoryTheory HomotopicalAlgebra

namespace HomotopicalAlgebra.FibrantBrownFactorization
variable {C : Type u} [Category.{v} C] [ModelCategory C]
  {X Y : C} (f : X ⟶ Y) (h : FibrantBrownFactorization f)

/-- The genuine retraction-section composite has an actual original right homotopy to the identity.
-/
theorem retractionSection_rightHomotopy [IsCofibrant h.Z] :
    RightHomotopyRel (h.r ≫ h.i) (𝟙 h.Z) := by
  have heq : LeftHomotopyClass.mk (h.r ≫ h.i) = LeftHomotopyClass.mk (𝟙 h.Z) :=
    (LeftHomotopyClass.postcomp_bijective_of_fibration_of_weakEquivalence h.Z h.r).injective
      (by simp only [LeftHomotopyClass.postcomp_mk, Category.assoc, h.i_r,
        Category.comp_id, Category.id_comp])
  exact ((LeftHomotopyClass.mk_eq_mk_iff _ _).mp heq).rightHomotopyRel

/-- The two actual original factor maps are endpoints of a whole good path-object map, with both
original
  endpoint equations. -/
theorem exists_good_pathComparison [IsFibrant Y] [IsCofibrant h.Z] :
    ∃ P : PathObject Y, P.IsGood ∧
      trivialFibrations C P.p₀ ∧ trivialFibrations C P.p₁ ∧
      ∃ q : h.Z ⟶ P.P, q ≫ P.p₀ = h.r ≫ f ∧ q ≫ P.p₁ = h.p := by
  have hrel := (retractionSection_rightHomotopy f h).postcomp h.p
  have hactual : RightHomotopyRel (h.r ≫ f) h.p := by
    simpa only [Category.assoc, h.fac, Category.id_comp] using hrel
  obtain ⟨P, hP, ⟨q⟩⟩ := hactual.exists_good_pathObject
  let _ : P.IsGood := hP
  exact ⟨P, hP, mem_trivialFibrations P.p₀, mem_trivialFibrations P.p₁, q.h, q.h₀, q.h₁⟩

end HomotopicalAlgebra.FibrantBrownFactorization
