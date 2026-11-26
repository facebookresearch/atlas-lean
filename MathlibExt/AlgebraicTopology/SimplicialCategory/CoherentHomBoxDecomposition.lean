/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentHomOpenBox
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentCompositionFace

/-!
# The actual coherent Hom box as original zero and composition faces

The box is exactly the union of whole path chains missing one retained
interior vertex or containing a middle vertex throughout. These are the
original coherent face and union-composition conditions at every scalar
degree, including degenerate simplices. The missing negative face has its
original distinguished label.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace CategoryTheory.CoherentRealization.HomBoxDecomposition
open IntervalHom HomBoxWords CubeCoordinates
variable {J : Type u} [LinearOrder J] {i j : J}

/-- The original negative coherent face: the supplied vertex is absent from the whole path chain. -/
def negative (i t j : J) : (nerve (SimplicialThickening.Path i j)).Subcomplex where
  obj q := {p | ∀ a, t ∉ (p.obj a).I}
  map f p hp := by
    intro a
    exact hp (f.unop.toOrderHom a)

/-- The box condition on the same entire original path chain and the same distinguished
interior vertex. -/
theorem mem_iff (hij : i ≤ j) (k : Interior i j) {q : SimplexCategoryᵒᵖ}
    (p : (nerve (SimplicialThickening.Path i j)).obj q) :
    p ∈ (HomOpenBox.subcomplex hij k).obj q ↔
      (∀ a, k.val ∈ (p.obj a).I) ∨
        ∃ t : CubeBoxes.Remaining k,
          (∀ a, t.val.val ∉ (p.obj a).I) ∨ (∀ a, t.val.val ∈ (p.obj a).I) :=
  HomOpenBox.mem_iff hij k p

/-- The actual coherent Hom-box subcomplex is exactly its retained negative and original
composition faces. -/
theorem subcomplex_eq (hij : i ≤ j) (k : Interior i j) :
    HomOpenBox.subcomplex hij k =
      CompositionFace.positive i k.val j ⊔
        ⨆ t : CubeBoxes.Remaining k,
          negative i t.val.val j ⊔ CompositionFace.positive i t.val.val j := by
  apply Subfunctor.ext
  funext q
  ext p
  rw [mem_iff]
  simp only [Subfunctor.max_obj, Subfunctor.iSup_obj, Set.mem_union, Set.mem_iUnion]
  rfl

/-- Every actual original composition face is retained in the box, including the
distinguished one. -/
theorem positive_le (hij : i ≤ j) (k t : Interior i j) :
    CompositionFace.positive i t.val j ≤ HomOpenBox.subcomplex hij k := by
  classical
  intro q p hp
  apply (mem_iff hij k p).mpr
  by_cases h : t = k
  · subst t
    exact Or.inl hp
  · exact Or.inr ⟨⟨t, h⟩, Or.inr hp⟩

/-- The retained negative face keeps its original label different from the missing interior
label. -/
theorem negative_le (hij : i ≤ j) (k t : Interior i j) (ht : t ≠ k) :
    negative i t.val j ≤ HomOpenBox.subcomplex hij k := by
  intro q p hp
  exact (mem_iff hij k p).mpr (Or.inr ⟨⟨t, ht⟩, Or.inl hp⟩)

end CategoryTheory.CoherentRealization.HomBoxDecomposition
