/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.ModelCategory.DerivedFunctorCoherence

/-!
# Associativity of the original left-derived replacement maps

The full counit naturality square retains each original Q and each original
left-functor map. It proves both complete source-derived compositor routes.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe uC uD uE uF vC vD vE vF
open CategoryTheory HomotopicalAlgebra
open CategoryTheory.Functor
open HomotopicalAlgebra.DerivedFunctorCoherence

namespace HomotopicalAlgebra.OriginalLeftDerivedAssociativity

variable {C : Type uC} [Category.{vC} C] [ModelCategory C]
  {D : Type uD} [Category.{vD} D] [ModelCategory D]
  {E : Type uE} [Category.{vE} E] [ModelCategory E]
  {F : Type uF} [Category.{vF} F] [ModelCategory F]
  (L : C ⥤ D) (M : D ⥤ E) (N : E ⥤ F)
  (qC : GeneratedFunctorialReplacements.Data (C := C))
  (qD : GeneratedFunctorialReplacements.Data (C := D))
  (qE : GeneratedFunctorialReplacements.Data (C := E))

/-- The two complete original counit words agree before any coefficient projection. -/
theorem raw_associativity (X : C) :
    (projection F).map (N.map (qE.Q.map (M.map (qD.q.app (L.obj (qC.Q.obj X)))))) ≫
        (projection F).map (N.map (qE.q.app (M.obj (L.obj (qC.Q.obj X))))) =
      (projection F).map (N.map (qE.q.app (M.obj (qD.Q.obj (L.obj (qC.Q.obj X)))))) ≫
        (projection F).map (N.map (M.map (qD.q.app (L.obj (qC.Q.obj X))))) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp]
  apply (projection F).congr_map
  apply N.congr_map
  exact qE.q.naturality (M.map (qD.q.app (L.obj (qC.Q.obj X))))

section Derived

variable {R : D ⥤ C} {S : E ⥤ D} {T : F ⥤ E}
  (a : L ⊣ R) [a.IsQuillenAdjunction]
  (b : M ⊣ S) [b.IsQuillenAdjunction]
  (c : N ⊣ T) [c.IsQuillenAdjunction]

/-- Both actual left-derived composition routes agree on every localized object and arrow. -/
theorem composition_associativity :
    whiskerRight (leftCompositionIso a b qC qD).hom (left c qE) ≫
        (leftCompositionIso (a.comp b) c qC qE).hom =
      whiskerLeft (left a qC) (leftCompositionIso b c qD qE).hom ≫
        (leftCompositionIso a (b.comp c) qC qD).hom := by
  apply Localization.natTrans_ext (projection C) (weakEquivalences C)
  intro X
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  change (left c qE).map ((leftCompositionIso a b qC qD).hom.app ((projection C).obj X)) ≫
      (leftCompositionIso (a.comp b) c qC qE).hom.app ((projection C).obj X) =
    (leftCompositionIso b c qD qE).hom.app ((projection D).obj (L.obj (qC.Q.obj X))) ≫
      (leftCompositionIso a (b.comp c) qC qD).hom.app ((projection C).obj X)
  rw [leftCompositionIso_app, leftCompositionIso_app, leftCompositionIso_app, leftCompositionIso_app]
  erw [left_map c qE (M.map (qD.q.app (L.obj (qC.Q.obj X))))]
  change (projection F).map (N.map (qE.Q.map (M.map (qD.q.app (L.obj (qC.Q.obj X)))))) ≫
      (projection F).map (N.map (qE.q.app (M.obj (L.obj (qC.Q.obj X))))) =
    (projection F).map (N.map (qE.q.app (M.obj (qD.Q.obj (L.obj (qC.Q.obj X)))))) ≫
      (projection F).map (N.map (M.map (qD.q.app (L.obj (qC.Q.obj X)))))
  exact raw_associativity L M N qC qD qE X

end Derived

end HomotopicalAlgebra.OriginalLeftDerivedAssociativity
