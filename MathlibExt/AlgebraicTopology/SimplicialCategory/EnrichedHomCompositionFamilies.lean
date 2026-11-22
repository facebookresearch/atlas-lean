/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.ProductFamilyVertexFibres
import MathlibExt.AlgebraicTopology.SimplicialCategory.EnrichedHomWeakTransport

/-!
# The SAME entire original enriched Hom composition families

Each full original enriched composition is retained together with its
entire parameter projection. Every original vertex restriction is its
actual original postcomposition action. A groupoid component category
makes those actions weak; when the whole original Homs are Kan, the
proved full fibre comparison detects the entire composition graph.
The source and target object universes are independent of coefficients.
-/

noncomputable section
universe u v w
open CategoryTheory MonoidalCategory CartesianMonoidalCategory Opposite
open scoped Simplicial

namespace CategoryTheory.SimplicialEnrichment.EnrichedHomCompositionFamilies
open ComponentCategory EnrichedHomVertexActions EnrichedHomWeakTransport
open SSet.ProductFamilyVertexFibres

variable {C : Type v} [EnrichedCategory SSet.{u} C]
variable {D : Type w} [EnrichedCategory SSet.{u} D]

/-- The actual complete original composition graph, with the original
whole Hom parameter preserved. -/
def postGraph (z x y : C) :
    (z ⟶[SSet.{u}] x) ⊗ (x ⟶[SSet.{u}] y) ⟶
      (z ⟶[SSet.{u}] y) ⊗ (x ⟶[SSet.{u}] y) :=
  graph (eComp SSet.{u} z x y)

/-- Its first projection retains every simplex of the SAME original composition. -/
@[reassoc]
lemma postGraph_fst (z x y : C) :
    postGraph z x y ≫ fst _ _ = eComp SSet.{u} z x y := graph_fst _

/-- Its second projection retains the full SAME original parameter Hom. -/
@[reassoc]
lemma postGraph_snd (z x y : C) : postGraph z x y ≫ snd _ _ = snd _ _ := graph_snd _

/-- The entire original constant-vertex section is the SAME native
unit-Hom tensor insertion in every ordinal degree. -/
lemma sectionAt_unit {X A : SSet.{u}} (a : A _⦋0⦌) :
    sectionAt X a = (ρ_ X).inv ≫ X ◁ (SSet.unitHomEquiv A).symm a := by
  apply CartesianMonoidalCategory.hom_ext
  · rw [sectionAt_fst, Category.assoc, whiskerLeft_fst]
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro t
    rfl
  · rw [sectionAt_snd]
    apply NatTrans.ext
    funext q
    apply ConcreteCategory.hom_ext
    intro t
    rfl

/-- Restricting the full original composition to a parameter vertex is
literally its SAME whole original postcomposition action. -/
lemma vertexAction_post (z x y : C) (a : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    vertexAction (eComp SSet.{u} z x y) a = post z ((SSet.unitHomEquiv _).symm a) := by
  rw [vertexAction, sectionAt_unit]
  rfl

/-- Every SAME original vertex action is weak for actual groupoid
components, without a Kan hypothesis. -/
theorem vertexAction_post_weak [IsGroupoid (objects.{u} C)]
    (z x y : C) (a : (x ⟶[SSet.{u}] y) _⦋0⦌) :
    SSet.realizationWeakEquivalences (vertexAction (eComp SSet.{u} z x y) a) := by
  let e := asIso (arrowOf C a)
  have hA : arrowOf C (SSet.unitHomEquiv _ ((SSet.unitHomEquiv _).symm a)) = e.hom :=
    congrArg (arrowOf C) ((SSet.unitHomEquiv _).apply_symm_apply a)
  rw [vertexAction_post]
  exact (post_weak_of_component_iso_representatives z e ((SSet.unitHomEquiv _).symm a)
    (inverseUnit e) hA (inverseUnit_class e)).1

/-- The full original composition graph is weak when its SAME three
whole original Hom objects are Kan and its original components form a groupoid. -/
theorem postGraph_weak_of_Kan [IsGroupoid (objects.{u} C)] (z x y : C)
    [SSet.KanComplex (z ⟶[SSet.{u}] x)] [SSet.KanComplex (z ⟶[SSet.{u}] y)]
    [SSet.KanComplex (x ⟶[SSet.{u}] y)] : SSet.realizationWeakEquivalences (postGraph z x y) :=
  graph_weak_of_vertexActions _ (vertexAction_post_weak z x y)

/-- Every original enriched functor preserves the SAME entire graph
family square, including its whole parameter Hom map. -/
theorem postGraph_natural (F : EnrichedFunctor SSet.{u} C D) (z x y : C) :
    postGraph z x y ≫ (F.map z y ⊗ₘ F.map x y) =
      (F.map z x ⊗ₘ F.map x y) ≫ postGraph (F.obj z) (F.obj x) (F.obj y) := by
  apply CartesianMonoidalCategory.hom_ext
  · simp only [Category.assoc, tensorHom_fst, postGraph_fst_assoc, postGraph_fst]
    exact F.map_comp z x y
  · simp only [Category.assoc, tensorHom_snd, postGraph_snd_assoc, postGraph_snd]

/-- The actual graph retains its complete coefficient and base word in
EVERY simplicial degree. -/
lemma postGraph_app (z x y : C) (q : SimplexCategoryᵒᵖ)
    (a : (z ⟶[SSet.{u}] x).obj q) (b : (x ⟶[SSet.{u}] y).obj q) :
    (postGraph z x y).app q (SSet.componentTensorSimplex q a b) =
      SSet.componentTensorSimplex q ((eComp SSet.{u} z x y).app q
        (SSet.componentTensorSimplex q a b)) b := rfl

end CategoryTheory.SimplicialEnrichment.EnrichedHomCompositionFamilies
