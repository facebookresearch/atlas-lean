/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.CategoryTheory.SmallObject.BoundaryOmegaIndex
import MathlibExt.CategoryTheory.SmallObject.CountableAttachmentSquares
import Mathlib.CategoryTheory.Category.Preorder
import Mathlib.Basic.Countable.Basic

/-!
# Focused clients for countable attachment squares and `ω`-stage indices

The cells `i ⟶ i + 1` of the thin category `WithTop ℕ`, attached along the
identity of `⊤`, have one attachment square for every natural number. The
`Countable` instance for `FunctorObjIndex` is found by `inferInstance`; together
with infinitude it gives an equivalence with `ℕ`. With uncountably many cells
indexed by `Set ℕ` the squares are uncountable, so the countability of the index
type cannot be dropped.

The natural-number stages of `ℵ₀.ord.ToType` start at `⊥`, follow successors,
are strictly increasing, and exhaust the order, so no stage is a successor limit.
-/

open CategoryTheory CategoryTheory.SmallObject

namespace MathlibExtTest.CategoryTheory.SmallObject.CountableStages

section AttachmentSquares

/-- Morphisms of the thin category `WithTop ℕ` form a subsingleton. -/
instance (a b : WithTop ℕ) : Countable (a ⟶ b) := by
  have : Subsingleton (a ⟶ b) := ⟨fun f g => Subsingleton.elim f g⟩
  infer_instance

/-- The cell `n ⟶ n + 1` of `WithTop ℕ`. -/
def cell (n : ℕ) : ((n : WithTop ℕ)) ⟶ ((n + 1 : ℕ) : WithTop ℕ) :=
  homOfLE (by exact_mod_cast Nat.le_succ n)

/-- Every cell has an attachment square along `𝟙 ⊤`. -/
def square (n : ℕ) : FunctorObjIndex cell (𝟙 (⊤ : WithTop ℕ)) where
  i := n
  t := homOfLE le_top
  b := homOfLE le_top
  w := Subsingleton.elim _ _

/-- The `Countable` instance applies to this concrete family by instance search. -/
example : Countable (FunctorObjIndex cell (𝟙 (⊤ : WithTop ℕ))) := inferInstance

lemma square_injective : Function.Injective square := by
  intro m n h
  exact congrArg FunctorObjIndex.i h

instance infinite_squares : Infinite (FunctorObjIndex cell (𝟙 (⊤ : WithTop ℕ))) :=
  Infinite.of_injective square square_injective

/-- The attachment squares are countably infinite. -/
example : Nonempty (FunctorObjIndex cell (𝟙 (⊤ : WithTop ℕ)) ≃ ℕ) :=
  nonempty_equiv_of_countable

/-- One cell `0 ⟶ 1` for every subset of `ℕ`. -/
def setCell (_ : Set ℕ) : ((0 : ℕ) : WithTop ℕ) ⟶ ((1 : ℕ) : WithTop ℕ) :=
  homOfLE (by exact_mod_cast Nat.zero_le 1)

/-- With uncountably many cells the attachment squares are uncountable:
the countability of the index type is a genuine hypothesis. -/
example : ¬ Countable (FunctorObjIndex setCell (𝟙 (⊤ : WithTop ℕ))) := by
  intro h
  obtain ⟨g, hg⟩ := h.exists_injective_nat
  let φ : Set ℕ → FunctorObjIndex setCell (𝟙 (⊤ : WithTop ℕ)) := fun s =>
    { i := s, t := homOfLE le_top, b := homOfLE le_top, w := Subsingleton.elim _ _ }
  have hφ : Function.Injective φ := fun s s' hs => congrArg FunctorObjIndex.i hs
  exact Function.cantor_injective (g ∘ φ) (hg.comp hφ)

end AttachmentSquares

section OmegaStages

attribute [local instance] Cardinal.orderBotAleph0OrdToType

/-- The third stage is the third successor of the bottom stage. -/
example : aleph0Stage.{0} 3 = Order.succ (Order.succ (Order.succ ⊥)) := by
  rw [aleph0Stage_succ, aleph0Stage_succ, aleph0Stage_succ, aleph0Stage_zero]

/-- Distinct natural numbers give distinct stages; in particular stage one is not `⊥`. -/
example : aleph0Stage.{0} 1 ≠ ⊥ := by
  rw [← aleph0Stage_zero.{0}]
  exact (aleph0Stage_strictMono.{0} Nat.zero_lt_one).ne'

/-- The order isomorphism is monotone in both directions. -/
example (m n : ℕ) : aleph0StageOrderIso.{0} m ≤ aleph0StageOrderIso n ↔ m ≤ n :=
  aleph0StageOrderIso.le_iff_le

/-- No stage of `ℵ₀.ord.ToType` is a successor limit: every stage is `⊥` or a successor. -/
example (j : Cardinal.aleph0.{0}.ord.ToType) : ¬ Order.IsSuccLimit j := by
  obtain ⟨n, rfl⟩ := aleph0Stage_surjective.{0} j
  cases n with
  | zero =>
    rw [aleph0Stage_zero]
    exact fun h => h.not_isMin isMin_bot
  | succ n =>
    rw [aleph0Stage_succ]
    exact fun h => h.isSuccPrelimit _ (Order.covBy_succ_of_not_isMax
      (not_isMax_of_lt (aleph0Stage_strictMono.{0} (Nat.lt_succ_self n))))

end OmegaStages

end MathlibExtTest.CategoryTheory.SmallObject.CountableStages
