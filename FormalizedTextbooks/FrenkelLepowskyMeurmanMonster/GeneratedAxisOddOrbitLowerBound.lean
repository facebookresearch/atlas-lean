/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisOddStabilizerProjection

/-! A genuine third-local-orbit lower bound using the actual Q kernel and physical line. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine restricted projection range has at most the actual Co1 line stabilizer order. -/
theorem generatedOddLocalAxisProjection_range_card_le :
    Nat.card generatedOddLocalAxisProjection.range ≤ 20891566080 := by
  let : Finite Co1 := co1_finite
  exact (Nat.card_le_card_of_injective (f := Subtype.val)
    Subtype.val_injective).trans_eq generatedNormEightCo1LineStabilizer_card

/-- The genuine H axis stabilizer has at most 85571854663680 elements. -/
theorem generatedOddLocalAxisStabilizer_card_le :
    Nat.card generatedOddLocalAxisStabilizer ≤ 85571854663680 := by
  have h := generatedOddLocalAxisProjection.ker.card_mul_index
  rw [Subgroup.index_ker, generatedOddLocalAxisProjection_kernel_card] at h
  calc
    Nat.card generatedOddLocalAxisStabilizer =
        2 ^ 12 * Nat.card generatedOddLocalAxisProjection.range := h.symm
    _ ≤ 2 ^ 12 * 20891566080 :=
      Nat.mul_le_mul_left _ generatedOddLocalAxisProjection_range_card_le
    _ = 85571854663680 := by norm_num

/-- The actual third local axis orbit contains at least 1630347264000 distinct axes. -/
theorem generatedOddLocalAxisOrbit_card_ge :
    1630347264000 ≤ Nat.card (MulAction.orbit H generatedOddAxis) := by
  have hc := generatedOddLocalAxisStabilizer.card_mul_index
  have h : 85571854663680 * 1630347264000 ≤
      85571854663680 * generatedOddLocalAxisStabilizer.index := by
    calc
      85571854663680 * 1630347264000 = Nat.card H := by
        rw [local_h_card_exact]
      _ = Nat.card generatedOddLocalAxisStabilizer * generatedOddLocalAxisStabilizer.index :=
        hc.symm
      _ ≤ 85571854663680 * generatedOddLocalAxisStabilizer.index :=
        Nat.mul_le_mul_right _ generatedOddLocalAxisStabilizer_card_le
  have hi : 1630347264000 ≤ generatedOddLocalAxisStabilizer.index := by omega
  rw [generatedOddLocalAxisStabilizer, MulAction.index_stabilizer,
    ← Nat.card_coe_set_eq] at hi
  exact hi

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
