/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorNaturalIso

/-!
# Naturality of the original right-derived compositor

The original R units prove compatibility with arbitrary transformations of
both original right functors. The same full derived transformations and
compositors occur on both sides, before any index or coefficient projection.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uC uD uE vC vD vE
open CategoryTheory HomotopicalAlgebra
open CategoryTheory.Functor
open HomotopicalAlgebra.DerivedFunctorCoherence

namespace HomotopicalAlgebra.OriginalRightDerivedCompositorNaturality

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) [a.IsQuillenAdjunction]
  {M : D ⥤ E} {S : E ⥤ D} (b : M ⊣ S) [b.IsQuillenAdjunction]
  (rD : GeneratedFunctorialReplacements.Data (C := D))
  (rE : GeneratedFunctorialReplacements.Data (C := E))

section OuterRightFunctor

variable {L' : C ⥤ D} {R' : D ⥤ C} (a' : L' ⊣ R') [a'.IsQuillenAdjunction]

/-- Every actual transformation of the outer right functor keeps both original compositor maps. -/
theorem outer_naturality (τ : R ⟶ R') :
    rightNat (a.comp b) (a'.comp b) rE (whiskerLeft S τ) ≫
        (rightCompositionIso a' b rD rE).hom =
      (rightCompositionIso a b rD rE).hom ≫
        whiskerLeft (right b rE) (rightNat a a' rD τ) := by
  apply Localization.natTrans_ext (projection E) (weakEquivalences E)
  intro X
  simp only [NatTrans.comp_app, whiskerLeft_app]
  change (rightNat (a.comp b) (a'.comp b) rE (whiskerLeft S τ)).app
        ((projection E).obj X) ≫
      (rightCompositionIso a' b rD rE).hom.app ((projection E).obj X) =
    (rightCompositionIso a b rD rE).hom.app ((projection E).obj X) ≫
      (rightNat a a' rD τ).app ((projection D).obj (S.obj (rE.R.obj X)))
  rw [rightNat_app, rightCompositionIso_app, rightCompositionIso_app, rightNat_app]
  change (projection C).map (τ.app (S.obj (rE.R.obj X))) ≫
      (projection C).map (R'.map (rD.r.app (S.obj (rE.R.obj X)))) =
    (projection C).map (R.map (rD.r.app (S.obj (rE.R.obj X)))) ≫
      (projection C).map (τ.app (rD.R.obj (S.obj (rE.R.obj X))))
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply (projection C).congr_map
  exact (τ.naturality (rD.r.app (S.obj (rE.R.obj X)))).symm

end OuterRightFunctor

section InnerRightFunctor

variable {M' : D ⥤ E} {S' : E ⥤ D} (b' : M' ⊣ S') [b'.IsQuillenAdjunction]

/-- Every original inner transformation retains its actual intermediate R-unit naturality square. -/
theorem inner_naturality (τ : S ⟶ S') :
    rightNat (a.comp b) (a.comp b') rE (whiskerRight τ R) ≫
        (rightCompositionIso a b' rD rE).hom =
      (rightCompositionIso a b rD rE).hom ≫
        whiskerRight (rightNat b b' rE τ) (right a rD) := by
  apply Localization.natTrans_ext (projection E) (weakEquivalences E)
  intro X
  simp only [NatTrans.comp_app, whiskerRight_app]
  rw [rightNat_app, rightCompositionIso_app, rightCompositionIso_app, rightNat_app]
  erw [right_map a rD (τ.app (rE.R.obj X))]
  change (projection C).map (R.map (τ.app (rE.R.obj X))) ≫
      (projection C).map (R.map (rD.r.app (S'.obj (rE.R.obj X)))) =
    (projection C).map (R.map (rD.r.app (S.obj (rE.R.obj X)))) ≫
      (projection C).map (R.map (rD.R.map (τ.app (rE.R.obj X))))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  apply (projection C).congr_map
  apply R.congr_map
  exact rD.r.naturality (τ.app (rE.R.obj X))

end InnerRightFunctor

end HomotopicalAlgebra.OriginalRightDerivedCompositorNaturality

namespace HomotopicalAlgebra.OriginalRightDerivedCompositorNaturality

section NativeEquality

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L : C ⥤ D} {L' : C ⥤ D} {R R' : D ⥤ C}
  (a : L ⊣ R) [a.IsQuillenAdjunction]
  (a' : L' ⊣ R') [a'.IsQuillenAdjunction]
  (rD : GeneratedFunctorialReplacements.Data (C := D))

/-- Equality of actual original right functors gives equality of their whole unchanged R lifts. -/
theorem rightFunctor_eq (h : R = R') : right a rD = right a' rD := by
  cases h
  rfl

/-- The actual derived transport of a native equality is the same full equality transport. -/
theorem rightNatIso_eqToIso (h : R = R') :
    rightNatIso a a' rD (eqToIso h) = eqToIso (rightFunctor_eq a a' rD h) := by
  cases h
  apply Iso.ext
  apply Localization.natTrans_ext (projection D) (weakEquivalences D)
  intro X
  rw [rightNatIso_hom_app]
  change (projection C).map (𝟙 (R.obj (rD.R.obj X))) = 𝟙 _
  exact (projection C).map_id _

end NativeEquality

end HomotopicalAlgebra.OriginalRightDerivedCompositorNaturality
