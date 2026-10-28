/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisRootEightPackedSignedWord

/-! Exact passage from one whole-word equation to all original signed coordinate equations. -/
@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option maxHeartbeats 8000000

/-- A complete linear word check and original integral bounds imply every original coordinate equation. -/
theorem generatedRootEight_packed_signed_linear {k : ℕ} (w : Fin k → ℕ) (t : ℕ)
    (c : Fin k → ℤ) (a G : ℤ) (hG : 0 < G)
    (hw : ∀ j, w j < 512 ^ 16) (ht : t < 512 ^ 16)
    (hd : ∀ i : Fin 16, G ∣
      ((∑ j : Fin k, c j * generatedRootEightPackedSignedDigit (w j) i) -
        a * generatedRootEightPackedSignedDigit t i))
    (hb : ∀ i : Fin 16,
      |(∑ j : Fin k, c j * generatedRootEightPackedSignedDigit (w j) i) -
        a * generatedRootEightPackedSignedDigit t i| < G * 512)
    (hword : (∑ j : Fin k, c j * generatedRootEightPackedSignedWord (w j)) =
      a * generatedRootEightPackedSignedWord t) :
    ∀ i : Fin 16, (∑ j : Fin k, c j * generatedRootEightPackedSignedDigit (w j) i) =
      a * generatedRootEightPackedSignedDigit t i := by
  let f : Fin 16 → ℤ := fun i =>
    (∑ j : Fin k, c j * generatedRootEightPackedSignedDigit (w j) i) -
      a * generatedRootEightPackedSignedDigit t i
  have hp : (∑ i : Fin 16, f i * (512 : ℤ) ^ i.val) = 0 := by
    calc
      _ = (∑ j : Fin k, c j * (∑ i : Fin 16,
          generatedRootEightPackedSignedDigit (w j) i * (512 : ℤ) ^ i.val)) -
        a * (∑ i : Fin 16, generatedRootEightPackedSignedDigit t i * (512 : ℤ) ^ i.val) := by
          dsimp [f]
          simp_rw [sub_mul, Finset.sum_mul]
          rw [Finset.sum_sub_distrib, Finset.sum_comm]
          simp only [Finset.mul_sum, mul_assoc]
      _ = 0 := by
        simp_rw [generatedRootEight_packed_signed_word _ (hw _),
          generatedRootEight_packed_signed_word t ht]
        exact sub_eq_zero.mpr hword
  have hz := generatedRootEight_packed_scaled_integer_zero 512 G (by norm_num) hG f hd hb hp
  intro i
  exact sub_eq_zero.mp (hz i)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
