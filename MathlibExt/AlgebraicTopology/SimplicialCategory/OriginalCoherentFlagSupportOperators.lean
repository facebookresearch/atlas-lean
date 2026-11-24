/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentTerminalFlagPreimages
import MathlibExt.AlgebraicTopology.SimplicialCategory.OriginalCoherentBeadOuterOperator

/-!
# Original operators on whole terminal-supported flags

The actual original outer operator restricts to the computed supports
through their native ordered preimages. Every coefficient flag keeps its
complete direct-image equation, and the whole original ordinal square
commutes at every selected vertex.
-/

noncomputable section

universe u

open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag.Operators

variable {n m : ℕ} {q : SimplexCategoryᵒᵖ}
variable (f : ⦋n⦌ ⟶ ⦋m⦌) (f₀ : f.toOrderHom 0 = 0)
  (f₁ : f.toOrderHom (Fin.last n) = Fin.last m)
  (p : (coefficientObject.{u} n).obj q) (r : (coefficientObject.{u} m).obj q)
  (h : (OuterOperator.map f f₀ f₁).app q p = r)

include f₀ f₁ h in
/-- A target flag contains precisely the images of the same original source flag. -/
theorem mem_target_flag (t : Fin (q.unop.len + 1)) (j : Fin (m + 1)) :
    ULift.up.{u} j ∈ (r.obj t).I ↔
      ∃ i : Fin (n + 1), ULift.up.{u} i ∈ (p.obj t).I ∧ f.toOrderHom i = j := by
  have he : f.toOrderHom.uliftMap '' (p.obj t).I = (r.obj t).I :=
    (OuterOperator.map_flags f f₀ f₁ p t).symm.trans
      (congrArg (fun a : (coefficientObject.{u} m).obj q => (a.obj t).I) h)
  rw [← he]
  constructor
  · rintro ⟨i, hi, he⟩
    exact ⟨i.down, hi, congrArg ULift.down he⟩
  · rintro ⟨i, hi, he⟩
    exact ⟨ULift.up i, hi, ULift.ext he⟩

include f₀ f₁ h in
/-- Each selected original source vertex has its actual supported target image. -/
theorem image_mem_support (i : Fin (dimension p + 1)) :
    f.toOrderHom (embedding p i) ∈ support r :=
  (mem_support r _).mpr
    ((mem_target_flag f f₀ f₁ p r h (Fin.last q.unop.len) _).mpr
      ⟨embedding p i,
        (mem_support p _).mp (Finset.orderEmbOfFin_mem (support p) (card_support p) i),
        rfl⟩)

/-- The actual selected target index of the same original image vertex. -/
def vertexMap (i : Fin (dimension p + 1)) : Fin (dimension r + 1) :=
  preimage r (f.toOrderHom (embedding p i)) (image_mem_support f f₀ f₁ p r h i)

/-- The selected target index reads back the same original outer image. -/
theorem vertexMap_image (i : Fin (dimension p + 1)) :
    embedding r (vertexMap f f₀ f₁ p r h i) = f.toOrderHom (embedding p i) :=
  embedding_preimage r _ _

/-- Restricting the same original outer map retains its actual vertex order. -/
theorem vertexMap_monotone : Monotone (vertexMap f f₀ f₁ p r h) := by
  intro i j hij
  apply (embedding r).le_iff_le.mp
  rw [vertexMap_image, vertexMap_image]
  exact f.toOrderHom.monotone ((embedding p).monotone hij)

/-- The actual selected original source index remains zero. -/
theorem vertexMap_zero : vertexMap f f₀ f₁ p r h 0 = 0 := by
  apply (embedding r).injective
  calc
    embedding r (vertexMap f f₀ f₁ p r h 0) =
        f.toOrderHom (embedding p 0) := vertexMap_image f f₀ f₁ p r h 0
    _ = 0 := (congrArg f.toOrderHom (embedding_zero p)).trans f₀
    _ = embedding r 0 := (embedding_zero r).symm

/-- The actual selected original target index remains the selected last vertex. -/
theorem vertexMap_last :
    vertexMap f f₀ f₁ p r h (Fin.last (dimension p)) = Fin.last (dimension r) := by
  apply (embedding r).injective
  calc
    embedding r (vertexMap f f₀ f₁ p r h (Fin.last (dimension p))) =
        f.toOrderHom (embedding p (Fin.last (dimension p))) :=
      vertexMap_image f f₀ f₁ p r h _
    _ = Fin.last m := (congrArg f.toOrderHom (embedding_last p)).trans f₁
    _ = embedding r (Fin.last (dimension r)) := (embedding_last r).symm

/-- The same actual outer operator on the complete selected original supports. -/
def operator : ⦋dimension p⦌ ⟶ ⦋dimension r⦌ :=
  SimplexCategory.Hom.mk
    ⟨vertexMap f f₀ f₁ p r h, vertexMap_monotone f f₀ f₁ p r h⟩

/-- The full original ordinal square commutes, with every original selected vertex retained. -/
theorem operator_embedding :
    TerminalFlag.operator p ≫ f =
      operator f f₀ f₁ p r h ≫ TerminalFlag.operator r := by
  ext i : 3
  exact (vertexMap_image f f₀ f₁ p r h i).symm

/-- The complete actual selected target flag is the image of the entire selected source flag. -/
theorem selected_flags_image (t : Fin (q.unop.len + 1)) :
    (operator f f₀ f₁ p r h).toOrderHom.uliftMap '' ((coefficient p).obj t).I =
      ((coefficient r).obj t).I := by
  ext j
  constructor
  · rintro ⟨i, hi, rfl⟩
    change liftedEmbedding r ((operator f f₀ f₁ p r h).toOrderHom.uliftMap i) ∈ (r.obj t).I
    have he : liftedEmbedding r ((operator f f₀ f₁ p r h).toOrderHom.uliftMap i) =
        ULift.up.{u} (f.toOrderHom (embedding p i.down)) :=
      ULift.ext (vertexMap_image f f₀ f₁ p r h i.down)
    rw [he]
    exact (mem_target_flag f f₀ f₁ p r h t _).mpr
      ⟨embedding p i.down, hi, rfl⟩
  · intro hj
    have hr : ULift.up.{u} (embedding r j.down) ∈ (r.obj t).I := hj
    obtain ⟨k, hk, hfk⟩ := (mem_target_flag f f₀ f₁ p r h t _).mp hr
    have hs : k ∈ support p :=
      (mem_support p k).mpr (flag_subset_last p t hk)
    have hrange : k ∈ Set.range (embedding p) := by
      rw [range_embedding]
      exact hs
    obtain ⟨i, hi⟩ := hrange
    have hpre : ULift.up.{u} i ∈ ((coefficient p).obj t).I := by
      change ULift.up.{u} (embedding p i) ∈ (p.obj t).I
      exact hi ▸ hk
    have he : vertexMap f f₀ f₁ p r h i = j.down := by
      apply (embedding r).injective
      calc
        embedding r (vertexMap f f₀ f₁ p r h i) =
            f.toOrderHom (embedding p i) := vertexMap_image f f₀ f₁ p r h i
        _ = f.toOrderHom k := congrArg f.toOrderHom hi
        _ = embedding r j.down := hfk
    exact ⟨ULift.up i, hpre, ULift.ext he⟩

private instance {J : Type u} [LinearOrder J] (i j : J)
    (a b : SimplicialThickening.Path i j) : Subsingleton (a ⟶ b) where
  allEq f g := by
    apply InducedCategory.Hom.ext
    exact Subsingleton.elim _ _

/-- The entire selected coefficient follows the same original restricted outer operator. -/
theorem coefficient_map :
    (OuterOperator.map (operator f f₀ f₁ p r h)
      (vertexMap_zero f f₀ f₁ p r h) (vertexMap_last f f₀ f₁ p r h)).app q
        (coefficient p) = coefficient r := by
  refine Functor.ext (fun t => ?_) ?_
  · apply SimplicialThickening.Path.ext
    exact selected_flags_image f f₀ f₁ p r h t
  · intro i j g
    exact Subsingleton.elim _ _

end CategoryTheory.CoherentRealization.OriginalBead.TerminalFlag.Operators
