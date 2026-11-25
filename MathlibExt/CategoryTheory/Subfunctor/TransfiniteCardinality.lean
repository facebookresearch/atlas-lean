/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.CategoryTheory.Subfunctor.Cardinality
public import MathlibExt.CategoryTheory.Subfunctor.TransfiniteUnion

/-!
# Cardinal bounds for strict-prefix subfunctor chains

Finite joins and strict-prefix unions of uniformly bounded subfunctors remain
bounded by the same infinite cardinal.  The order lemmas retain the literal
seed at its next stage.  These are the cardinal and inclusion calculations
used by bounded transfinite closure arguments.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section

universe u

open Cardinal CategoryTheory

namespace CategoryTheory.Subfunctor

variable {C : Type} [SmallCategory C] {F : Cᵒᵖ ⥤ Type u}

/-- The join of two original subfunctors bounded by the same infinite cardinal
is bounded by that cardinal. -/
theorem mk_elements_sup_le_of_le (A B : Subfunctor F) {γ : Cardinal.{u}}
    (hγ : ℵ₀ ≤ γ)
    (hA : Cardinal.mk A.toFunctor.Elements ≤ γ)
    (hB : Cardinal.mk B.toFunctor.Elements ≤ γ) :
    Cardinal.mk (A ⊔ B).toFunctor.Elements ≤ γ := by
  let S : ULift.{u} Bool → Subfunctor F := fun b => if b.down then A else B
  have hS : A ⊔ B = ⨆ b, S b := by
    apply le_antisymm
    · apply sup_le
      · exact le_iSup_of_le (ULift.up true) (by simp [S])
      · exact le_iSup_of_le (ULift.up false) (by simp [S])
    · apply iSup_le
      rintro ⟨b⟩
      cases b <;> simp [S]
  rw [hS]
  have hSindex : Cardinal.mk (ULift.{u} Bool) ≤ γ :=
    Cardinal.mk_le_aleph0.trans hγ
  apply mk_elements_iSup_le_of_le (F := F) S hγ hSindex
  rintro ⟨b⟩
  cases b <;> simpa [S]

variable {J : Type u} [LinearOrder J]

/-- A strict-prefix union is bounded when its initial object, all earlier
seeds, and the earlier-stage index are bounded by the same infinite cardinal. -/
theorem mk_elements_strictPrefixUnion_le (A : Subfunctor F)
    (B : J → Subfunctor F) (j : J) {γ : Cardinal.{u}}
    (hγ : ℵ₀ ≤ γ)
    (hA : Cardinal.mk A.toFunctor.Elements ≤ γ)
    (hindex : Cardinal.mk (Set.Iio j) ≤ γ)
    (hB : ∀ k : Set.Iio j,
      Cardinal.mk (B k.1).toFunctor.Elements ≤ γ) :
    Cardinal.mk (strictPrefixUnion A B j).toFunctor.Elements ≤ γ := by
  apply mk_elements_sup_le_of_le A (⨆ k : Set.Iio j, B k.1) hγ hA
  exact mk_elements_iSup_le_of_le (F := F) (fun k : Set.Iio j => B k.1)
    hγ hindex hB

variable [SuccOrder J]

/-- The seed at `j` is literally present in the strict-prefix stage at the
successor of `j`. -/
theorem seed_le_strictPrefixUnion_succ (A : Subfunctor F)
    (B : J → Subfunctor F) (j : J) (hj : ¬ IsMax j) :
    B j ≤ strictPrefixUnion A B (Order.succ j) := by
  apply le_trans ?_ le_sup_right
  exact le_iSup_of_le
    (⟨j, Order.lt_succ_of_not_isMax hj⟩ : Set.Iio (Order.succ j)) le_rfl

/-- Every strict-prefix stage includes into its literal successor stage. -/
theorem strictPrefixUnion_le_succ (A : Subfunctor F)
    (B : J → Subfunctor F) (j : J) :
    strictPrefixUnion A B j ≤ strictPrefixUnion A B (Order.succ j) :=
  strictPrefixUnion_mono A B (Order.le_succ j)

end CategoryTheory.Subfunctor
