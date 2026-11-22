/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorNaturalIso

/-!
# Naturality of the original left-derived compositor

The original Q counits prove compatibility with transformations of both left
functors, retaining the complete derived maps and native equality transports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uC uD uE vC vD vE
open CategoryTheory HomotopicalAlgebra
open CategoryTheory.Functor
open HomotopicalAlgebra.DerivedFunctorCoherence

namespace HomotopicalAlgebra.OriginalLeftDerivedCompositorNaturality

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {L : C ⥤ D} {R : D ⥤ C} (a : L ⊣ R) [a.IsQuillenAdjunction]
  {M : D ⥤ E} {S : E ⥤ D} (b : M ⊣ S) [b.IsQuillenAdjunction]
  (qC : GeneratedFunctorialReplacements.Data (C := C))
  (qD : GeneratedFunctorialReplacements.Data (C := D))

section InnerLeftFunctor

variable {L' : C ⥤ D} {R' : D ⥤ C} (a' : L' ⊣ R') [a'.IsQuillenAdjunction]

/-- Every original inner transformation retains its actual intermediate Q-counit square. -/
theorem inner_naturality (τ : L ⟶ L') :
    whiskerRight (leftNat a a' qC τ) (left b qD) ≫
        (leftCompositionIso a' b qC qD).hom =
      (leftCompositionIso a b qC qD).hom ≫
        leftNat (a.comp b) (a'.comp b) qC (whiskerRight τ M) := by
  apply Localization.natTrans_ext (projection C) (weakEquivalences C)
  intro X
  simp only [NatTrans.comp_app, whiskerRight_app]
  rw [leftNat_app, leftCompositionIso_app, leftCompositionIso_app, leftNat_app]
  erw [left_map b qD (τ.app (qC.Q.obj X))]
  change (projection E).map (M.map (qD.Q.map (τ.app (qC.Q.obj X)))) ≫
      (projection E).map (M.map (qD.q.app (L'.obj (qC.Q.obj X)))) =
    (projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X)))) ≫
      (projection E).map (M.map (τ.app (qC.Q.obj X)))
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  apply (projection E).congr_map
  apply M.congr_map
  exact qD.q.naturality (τ.app (qC.Q.obj X))

end InnerLeftFunctor

section OuterLeftFunctor

variable {M' : D ⥤ E} {S' : E ⥤ D} (b' : M' ⊣ S') [b'.IsQuillenAdjunction]

/-- Every actual outer transformation keeps both complete original Q-compositor maps. -/
theorem outer_naturality (τ : M ⟶ M') :
    whiskerLeft (left a qC) (leftNat b b' qD τ) ≫
        (leftCompositionIso a b' qC qD).hom =
      (leftCompositionIso a b qC qD).hom ≫
        leftNat (a.comp b) (a.comp b') qC (whiskerLeft L τ) := by
  apply Localization.natTrans_ext (projection C) (weakEquivalences C)
  intro X
  simp only [NatTrans.comp_app, whiskerLeft_app]
  change (leftNat b b' qD τ).app ((projection D).obj (L.obj (qC.Q.obj X))) ≫
      (leftCompositionIso a b' qC qD).hom.app ((projection C).obj X) =
    (leftCompositionIso a b qC qD).hom.app ((projection C).obj X) ≫
      (leftNat (a.comp b) (a.comp b') qC (whiskerLeft L τ)).app ((projection C).obj X)
  rw [leftNat_app, leftCompositionIso_app, leftCompositionIso_app, leftNat_app]
  change (projection E).map (τ.app (qD.Q.obj (L.obj (qC.Q.obj X)))) ≫
      (projection E).map (M'.map (qD.q.app (L.obj (qC.Q.obj X)))) =
    (projection E).map (M.map (qD.q.app (L.obj (qC.Q.obj X)))) ≫
      (projection E).map (τ.app (L.obj (qC.Q.obj X)))
  rw [← Functor.map_comp, ← Functor.map_comp]
  apply (projection E).congr_map
  exact (τ.naturality (qD.q.app (L.obj (qC.Q.obj X)))).symm

end OuterLeftFunctor

end HomotopicalAlgebra.OriginalLeftDerivedCompositorNaturality

namespace HomotopicalAlgebra.OriginalLeftDerivedCompositorNaturality

section NativeEquality

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {L L' : C ⥤ D} {R : D ⥤ C} {R' : D ⥤ C}
  (a : L ⊣ R) [a.IsQuillenAdjunction]
  (a' : L' ⊣ R') [a'.IsQuillenAdjunction]
  (qC : GeneratedFunctorialReplacements.Data (C := C))

/-- Equality of actual left functors gives equality of their whole unchanged source Q lifts. -/
theorem leftFunctor_eq (h : L = L') : left a qC = left a' qC := by
  cases h
  rfl

/-- The actual derived transport of native equality is the same whole Q-lift equality transport. -/
theorem leftNatIso_eqToIso (h : L = L') :
    leftNatIso a a' qC (eqToIso h) = eqToIso (leftFunctor_eq a a' qC h) := by
  cases h
  apply Iso.ext
  apply Localization.natTrans_ext (projection C) (weakEquivalences C)
  intro X
  rw [leftNatIso_hom_app]
  change (projection D).map (𝟙 (L.obj (qC.Q.obj X))) = 𝟙 _
  exact (projection D).map_id _

end NativeEquality

end HomotopicalAlgebra.OriginalLeftDerivedCompositorNaturality
