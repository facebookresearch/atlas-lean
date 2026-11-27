/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua
import MathlibExt.AlgebraicTopology.SimplicialCategory.CoherentRightCubeOrdinalEmbedding

/-!
# Actual injected images of least-vertex normalized supports

An order embedding need not preserve the least vertex. Nevertheless,
adjoining the actual target least vertex and cutting at the embedded
retained label detects the same source cut. This is the concrete set
geometry needed for original right-cube face injectivity.
-/

noncomputable section
universe u v
open CategoryTheory

namespace CategoryTheory.CoherentRealization.NormalizedOrderImage
variable {J : Type u} {K : Type v} [LinearOrder J] [OrderBot J] [LinearOrder K] [OrderBot K]

/-- The actual retained source support, with its original least vertex adjoined. -/
def cut (a : J) (S : Set J) : Set J := {⊥} ∪ {x | x ∈ S ∧ a ≤ x}

/-- The actual target support after original direct image, least-vertex adjunction and
cutting at the same
  embedded label. -/
def imageCut (e : J ↪o K) (a : J) (S : Set J) : Set K := {⊥} ∪ {y | y ∈ e '' S ∧ e a ≤ y}

/-- A genuine order embedding cannot send a nonleast original source label to the target
least label. -/
theorem image_ne_bot (e : J ↪o K) {x : J} (hx : x ≠ ⊥) : e x ≠ ⊥ := by
  intro h
  have he : e (⊥ : J) = e x := le_antisymm (e.monotone bot_le) (h.symm ▸ bot_le)
  exact hx (e.injective he).symm

/-- Every nonleast original source label is retained precisely when its actual embedded
target label is retained. -/
theorem mem_imageCut_iff (e : J ↪o K) (a : J) (S : Set J) {x : J} (hx : x ≠ ⊥) :
    e x ∈ imageCut e a S ↔ x ∈ cut a S := by
  change (e x = ⊥ ∨ (e x ∈ e '' S ∧ e a ≤ e x)) ↔ (x = ⊥ ∨ (x ∈ S ∧ a ≤ x))
  constructor
  · rintro (h | ⟨⟨y, hy, he⟩, ha⟩)
    · exact False.elim (image_ne_bot e hx h)
    · have hxy : y = x := e.injective he
      exact Or.inr ⟨hxy ▸ hy, (e.map_rel_iff').mp ha⟩
  · rintro (h | ⟨hs, ha⟩)
    · exact False.elim (hx h)
    · exact Or.inr ⟨⟨x, hs, rfl⟩, e.monotone ha⟩

/-- Equality of actual normalized embedded supports reflects equality of the whole original
source cuts. -/
theorem cut_injective (e : J ↪o K) (a : J) (S T : Set J)
    (h : imageCut e a S = imageCut e a T) : cut a S = cut a T := by
  ext x
  by_cases hx : x = ⊥
  · subst x
    simp only [cut, Set.mem_union, Set.mem_singleton_iff, true_or]
  · rw [← mem_imageCut_iff e a S hx, h, mem_imageCut_iff e a T hx]

omit [OrderBot J] in
/-- The original target zero adjunction contributes no extra retained support beyond its
same actual outer
  least vertex. -/
theorem imageCut_zero_adjunction (e : J ↪o K) (a : J) (S : Set J) :
    {⊥} ∪ {y | y ∈ ({⊥} ∪ e '' S) ∧ e a ≤ y} = imageCut e a S := by
  ext y
  change (y = ⊥ ∨ ((y = ⊥ ∨ y ∈ e '' S) ∧ e a ≤ y)) ↔
    (y = ⊥ ∨ (y ∈ e '' S ∧ e a ≤ y))
  constructor
  · rintro (h₀ | ⟨h₀ | hs, ha⟩)
    · exact Or.inl h₀
    · exact Or.inl h₀
    · exact Or.inr ⟨hs, ha⟩
  · rintro (h₀ | ⟨hs, ha⟩)
    · exact Or.inl h₀
    · exact Or.inr ⟨Or.inr hs, ha⟩

end CategoryTheory.CoherentRealization.NormalizedOrderImage
