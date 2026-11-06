/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPositiveFinalShortCacheData
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightCanonicalShortCacheData

/-! Exact support cardinalities split into complete bounded original address intervals. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The complete original support predicate, with the final unused addresses excluded. -/
def generatedRootEightShortSupportBlockPredicate (f : GriessShortIndex → ℤ)
    (bu : Fin 96 × Fin 1024) : Prop :=
  1024 * bu.1.val + bu.2.val < 98280 ∧
    f (generatedNinthLowerSpinShortIndex
      ⟨(1024 * bu.1.val + bu.2.val) % 98280, Nat.mod_lt _ (by decide)⟩) ≠ 0

/-- The original finite predicate has its ordinary computational decision procedure. -/
instance (f : GriessShortIndex → ℤ) (bu : Fin 96 × Fin 1024) :
    Decidable (generatedRootEightShortSupportBlockPredicate f bu) := by
  unfold generatedRootEightShortSupportBlockPredicate
  infer_instance

/-- Every original nonzero short coordinate occurs exactly once in the bounded blocks. -/
def generatedRootEightShortSupportBlocksEquiv (f : GriessShortIndex → ℤ) :
    {r : GriessShortIndex // f r ≠ 0} ≃
      {bu : Fin 96 × Fin 1024 // generatedRootEightShortSupportBlockPredicate f bu} where
  toFun r := by
    let a := generatedNinthLowerSpinShortAddress r.val
    let b : Fin 96 := ⟨a.val / 1024, by have ha := a.isLt; omega⟩
    let u : Fin 1024 := ⟨a.val % 1024, Nat.mod_lt _ (by decide)⟩
    have hs : 1024 * b.val + u.val = a.val := by dsimp [b, u]; omega
    refine ⟨(b, u), ?_⟩
    unfold generatedRootEightShortSupportBlockPredicate
    refine ⟨by dsimp; omega, ?_⟩
    have hi : (⟨(1024 * b.val + u.val) % 98280, Nat.mod_lt _ (by decide)⟩ : Fin 98280) = a := by
      apply Fin.ext
      simp only [hs, Nat.mod_eq_of_lt a.isLt]
    rw [hi, generatedNinth_lower_spin_short_index_address]
    exact r.property
  invFun bu := ⟨generatedNinthLowerSpinShortIndex
    ⟨(1024 * bu.val.1.val + bu.val.2.val) % 98280, Nat.mod_lt _ (by decide)⟩,
    bu.property.2⟩
  left_inv r := by
    apply Subtype.ext
    dsimp
    have hs' : 1024 * ((generatedNinthLowerSpinShortAddress r.val).val / 1024) +
        (generatedNinthLowerSpinShortAddress r.val).val % 1024 =
        (generatedNinthLowerSpinShortAddress r.val).val := by omega
    simp only [hs', Nat.mod_eq_of_lt (generatedNinthLowerSpinShortAddress r.val).isLt]
    exact generatedNinth_lower_spin_short_index_address r.val
  right_inv bu := by
    apply Subtype.ext
    apply Prod.ext <;> apply Fin.ext
    all_goals
      dsimp
      rw [generatedNinth_lower_spin_short_address_index]
      simp only [Nat.mod_eq_of_lt bu.property.1]
      have hb := bu.val.1.isLt
      have hu := bu.val.2.isLt
      omega

/-- Count one complete block, excluding only the actual unused final addresses. -/
def generatedRootEightShortSupportBlockCount (f : GriessShortIndex → ℤ) (b : Fin 96) : ℕ :=
  ∑ u : Fin 1024, if generatedRootEightShortSupportBlockPredicate f (b, u) then 1 else 0

/-- Complete original support cardinality equals the sum of all bounded counts. -/
theorem generatedRootEight_short_support_card_blocks (f : GriessShortIndex → ℤ) :
    Nat.card {r : GriessShortIndex // f r ≠ 0} =
      ∑ b : Fin 96, generatedRootEightShortSupportBlockCount f b := by
  rw [Nat.card_congr (generatedRootEightShortSupportBlocksEquiv f), Nat.card_eq_fintype_card,
    Fintype.card_subtype, Finset.card_filter, Fintype.sum_prod_type]
  rfl

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
