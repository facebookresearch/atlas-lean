/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicTopology.SimplicialSet.Boundary
import Mathlib.CategoryTheory.Limits.Types.Coproducts
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts

/-!
# The original first face and first vertex have a monic coproduct inclusion

The whole right face of the original simplex has all vertex values
positive, while the original first vertex has value zero everywhere.
Their native coproduct embeds monomorphically, retaining both original
inclusion maps in every degree.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Simplicial

namespace SSet.FirstFaceVertexUnion

/-- The entire original right face of the same simplex. -/
def face (n : ℕ) : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.stdSimplex.map (SimplexCategory.δ (0 : Fin (n + 2)))

/-- The original first vertex of the same whole simplex. -/
def vertex (n : ℕ) : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
  SSet.stdSimplex.map (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk (n + 1)) 0)

/-- The whole native coproduct of the original first face and first vertex enters the same simplex. -/
def inclusion (n : ℕ) : (Δ[n] : SSet.{u}) ⨿ (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] :=
  coprod.desc (face n) (vertex n)

/-- Both entire original source inclusions remain exact. -/
theorem inclusion_legs (n : ℕ) :
    coprod.inl ≫ inclusion.{u} n = face.{u} n ∧ coprod.inr ≫ inclusion.{u} n = vertex.{u} n :=
  ⟨coprod.inl_desc _ _, coprod.inr_desc _ _⟩

/-- Evaluate the original whole coproduct as its actual sum of original simplex sets. -/
def sumToCoproductIso (n : ℕ) (d : SimplexCategoryᵒᵖ) :
    ((Δ[n] : SSet.{u}).obj d ⊕ (Δ[0] : SSet.{u}).obj d) ≅
      (((Δ[n] : SSet.{u}) ⨿ (Δ[0] : SSet.{u})).obj d) :=
  IsColimit.coconePointUniqueUpToIso
    (Types.binaryCoproductColimit _ _)
    (isColimitOfHasBinaryCoproductOfPreservesColimit (SSet.evaluation.obj d)
      (Δ[n] : SSet.{u}) (Δ[0] : SSet.{u}))

/-- The whole evaluated sum comparison retains the original first coproduct inclusion. -/
theorem sumToCoproductIso_inl (n : ℕ) (d : SimplexCategoryᵒᵖ) :
    (↾Sum.inl) ≫ (sumToCoproductIso.{u} n d).hom =
      (coprod.inl : (Δ[n] : SSet.{u}) ⟶ _).app d :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (Types.binaryCoproductColimit _ _)
    (isColimitOfHasBinaryCoproductOfPreservesColimit (SSet.evaluation.obj d)
      (Δ[n] : SSet.{u}) (Δ[0] : SSet.{u})) ⟨WalkingPair.left⟩

/-- The whole evaluated sum comparison retains the original point coproduct inclusion. -/
theorem sumToCoproductIso_inr (n : ℕ) (d : SimplexCategoryᵒᵖ) :
    (↾Sum.inr) ≫ (sumToCoproductIso.{u} n d).hom =
      (coprod.inr : (Δ[0] : SSet.{u}) ⟶ _).app d :=
  IsColimit.comp_coconePointUniqueUpToIso_hom (Types.binaryCoproductColimit _ _)
    (isColimitOfHasBinaryCoproductOfPreservesColimit (SSet.evaluation.obj d)
      (Δ[n] : SSet.{u}) (Δ[0] : SSet.{u})) ⟨WalkingPair.right⟩

/-- The original whole first-face map is injective on its exact original simplices. -/
theorem face_app_injective (n : ℕ) (d : SimplexCategoryᵒᵖ) :
    Function.Injective ((face.{u} n).app d) := by
  intro x y h
  apply stdSimplex.objEquiv.injective
  apply SimplexCategory.Hom.ext
  apply OrderHom.ext
  funext i
  have hi := congrArg (fun z => stdSimplex.asOrderHom z i) h
  change (stdSimplex.asOrderHom x i).succ = (stdSimplex.asOrderHom y i).succ at hi
  exact Fin.succ_inj.mp hi

/-- The whole original face and first-vertex images are disjoint in every degree. -/
theorem face_ne_vertex (n : ℕ) (d : SimplexCategoryᵒᵖ)
    (x : (Δ[n] : SSet.{u}).obj d) (y : (Δ[0] : SSet.{u}).obj d) :
    (face n).app d x ≠ (vertex n).app d y := by
  intro h
  have hi := congrArg (fun z => stdSimplex.asOrderHom z (0 : Fin (d.unop.len + 1))) h
  change (stdSimplex.asOrderHom x 0).succ = (0 : Fin (n + 2)) at hi
  exact Fin.succ_ne_zero _ hi

/-- The native coproduct inclusion is monic on every whole original simplex degree. -/
theorem inclusion_mono (n : ℕ) : Mono (inclusion.{u} n) := by
  rw [NatTrans.mono_iff_mono_app]
  intro d
  rw [CategoryTheory.mono_iff_injective]
  intro x y h
  let e := (sumToCoproductIso.{u} n d).toEquiv
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  have hl (z : (Δ[n] : SSet.{u}).obj d) :
      (inclusion n).app d (e (Sum.inl z)) = (face n).app d z := by
    have he := ConcreteCategory.congr_hom (sumToCoproductIso_inl.{u} n d) z
    have hf := ConcreteCategory.congr_hom
      (congrArg (fun q : (Δ[n] : SSet.{u}) ⟶ Δ[n + 1] => q.app d) (inclusion_legs.{u} n).1) z
    exact (congrArg ((inclusion n).app d) he).trans hf
  have hr (z : (Δ[0] : SSet.{u}).obj d) :
      (inclusion n).app d (e (Sum.inr z)) = (vertex n).app d z := by
    have he := ConcreteCategory.congr_hom (sumToCoproductIso_inr.{u} n d) z
    have hf := ConcreteCategory.congr_hom
      (congrArg (fun q : (Δ[0] : SSet.{u}) ⟶ Δ[n + 1] => q.app d) (inclusion_legs.{u} n).2) z
    exact (congrArg ((inclusion n).app d) he).trans hf
  rcases a with (a | a) <;> rcases b with (b | b)
  · exact congrArg (fun z => e (Sum.inl z)) (face_app_injective n d ((hl a).symm.trans (h.trans (hl b))))
  · exact (face_ne_vertex n d a b ((hl a).symm.trans (h.trans (hr b)))).elim
  · exact (face_ne_vertex n d b a ((hl b).symm.trans (h.symm.trans (hr a)))).elim
  · have hab : a = b := by
      apply stdSimplex.objEquiv.injective
      exact SimplexCategory.isTerminalZero.hom_ext _ _
    exact congrArg (fun z => e (Sum.inr z)) hab

end SSet.FirstFaceVertexUnion
