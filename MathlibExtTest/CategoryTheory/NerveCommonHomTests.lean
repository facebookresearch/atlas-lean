/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.CategoryTheory.NerveHomotopy
public import MathlibExt.AlgebraicTopology.SimplicialSet.NerveEquivalenceWeakEquivalence

/-!
# Native common-Hom nerve consumers

The classifier retains the actual transformation on its cross edge at independent source and
target universes. A distinct third category tests composition, and the positive-Hom corner
keeps object level zero while its morphisms live at level one.
-/

universe uSource uTarget vSource vTarget uObj vObj wHom

@[expose] public section

noncomputable section

open CategoryTheory Opposite
open scoped CategoryTheory.Prod Simplicial

namespace MathlibExtTest.CategoryTheory.NerveCommonHomTests

/-- The classified cross edge is the given transformation component, not an identity edge. -/
theorem classifier_cross_edge_retains_component
    {A : Type uSource} {B : Type uTarget}
    [Category.{vSource} A] [Category.{vTarget} B]
    {F G : A ⥤ B} (α : F ⟶ G) (a : A) :
    (NatTrans.nerveCylinderFunctor α).map
        (𝟙 a ×ₘ homOfLE (show (0 : Fin 2) ≤ 1 from by decide)) = α.app a := by
  simp [NatTrans.nerveCylinderFunctor, Functor.comp_map, Prod.swap_map,
    Functor.uncurry_obj_map, ComposableArrows.mk₁]

/-- The up/down composite retains vertices in a third, independently given low category. -/
theorem up_down_vertex_in_distinct_target
    {A D : Type uObj} [Category.{max vObj wHom} A] [Category.{max vObj wHom} D]
    {B : Type (max uObj vObj)} [Category.{max vObj wHom} B]
    (F : A ⥤ B) (G : B ⥤ D) (a : A) :
    ((nerveMapCommonHomUp.{uObj, vObj, wHom} F ≫
        nerveMapCommonHom.{uObj, vObj, wHom} G).app (op ⦋0⦌))
      (ComposableArrows.mk₀ a) = ComposableArrows.mk₀ (G.obj (F.obj a)) := by
  rw [nerveMapCommonHomUp_comp]
  exact ComposableArrows.ext₀ rfl

/-- Object level zero and Hom level one are retained by the actual categorical equivalence. -/
theorem equivalence_positive_Hom_without_object_raise
    {A B : Type 0} [Category.{1} A] [Category.{1} B] (e : A ≌ B) :
    SSet.realizationWeakEquivalences (nerveMapCommonHomUp.{0, 0, 1} e.functor) :=
  nerveMapCommonHomUp_mem_realizationWeakEquivalences_of_isEquivalence e.functor

section LegacyPositionalUniverses

universe uLegacy vLegacy

/-- The former explicit Hom/object prefix retains both vertices and the actual cross edge. -/
theorem classifier_legacy_positional_universes
    {A B : Type uLegacy} [Category.{vLegacy} A] [Category.{vLegacy} B]
    {F G : A ⥤ B} (α : F ⟶ G) (a : A) :
    (NatTrans.nerveCylinderFunctor.{vLegacy, uLegacy} α).obj (a, 0) = F.obj a ∧
    (NatTrans.nerveCylinderFunctor.{vLegacy, uLegacy} α).obj (a, 1) = G.obj a ∧
    (NatTrans.nerveCylinderFunctor.{vLegacy, uLegacy} α).map
        (𝟙 a ×ₘ homOfLE (show (0 : Fin 2) ≤ 1 from by decide)) = α.app a := by
  refine ⟨NatTrans.nerveCylinderFunctor_obj_zero α a,
    NatTrans.nerveCylinderFunctor_obj_one α a, ?_⟩
  exact classifier_cross_edge_retains_component α a

end LegacyPositionalUniverses

#print axioms classifier_cross_edge_retains_component
#print axioms up_down_vertex_in_distinct_target
#print axioms equivalence_positive_Hom_without_object_raise
#print axioms classifier_legacy_positional_universes

end MathlibExtTest.CategoryTheory.NerveCommonHomTests

end
