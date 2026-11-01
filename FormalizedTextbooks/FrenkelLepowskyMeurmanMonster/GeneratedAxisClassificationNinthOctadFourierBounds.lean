/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.TrialityOrder

/-! Bounds for the original signed octad Fourier transform. Two source terms use the
triangle inequality. Four source terms whose label XOR is zero and whose sign product is
negative have bounded sums at every Fourier row. No axis coefficient is assumed. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- Every entry of the original integer octad Fourier matrix has absolute value one. -/
theorem generatedNinth_octad_fourier_entry_abs (e f : Fin 64) :
    |trialityIntegerMatrix e f| = 1 := by
  have hd : |trialityIntegerDiagonal e| = 1 := by
    unfold trialityIntegerDiagonal
    split <;> norm_num
  have hh : |trialityHadamard e f| = 1 := by
    unfold trialityHadamard
    split <;> norm_num
  simp only [trialityIntegerMatrix, abs_mul, hd, hh, mul_one]

/-- The original Fourier row is a character of XOR on the even octad representatives. -/
theorem generatedNinth_octad_hadamard_xor_right (e a b : Fin 64) :
    trialityHadamard e (trialityXor a b) =
      trialityHadamard e a * trialityHadamard e b := by
  rw [trialityHadamard_symmetric, trialityHadamard_xor,
    trialityHadamard_symmetric a e, trialityHadamard_symmetric b e]

/-- Four Fourier entries whose original labels XOR to zero have product one. -/
theorem generatedNinth_octad_fourier_four_product (e a b c d : Fin 64)
    (hzero : trialityXor (trialityXor a b) (trialityXor c d) = 0) :
    trialityIntegerMatrix e a * trialityIntegerMatrix e b *
      trialityIntegerMatrix e c * trialityIntegerMatrix e d = 1 := by
  have hh : (trialityHadamard e a * trialityHadamard e b) *
      (trialityHadamard e c * trialityHadamard e d) = 1 := by
    calc
      _ = trialityHadamard e (trialityXor (trialityXor a b) (trialityXor c d)) := by
        rw [generatedNinth_octad_hadamard_xor_right,
          generatedNinth_octad_hadamard_xor_right, generatedNinth_octad_hadamard_xor_right]
      _ = 1 := by
        rw [hzero]
        simp [trialityHadamard, trialityEvenMask, trialityBitWeight8]
  have hd : trialityIntegerDiagonal e ^ 4 = 1 := by
    calc
      _ = (trialityIntegerDiagonal e * trialityIntegerDiagonal e) *
          (trialityIntegerDiagonal e * trialityIntegerDiagonal e) := by ring
      _ = 1 := by rw [trialityIntegerDiagonal_sq]; norm_num
  calc
    _ = trialityIntegerDiagonal e ^ 4 *
        ((trialityHadamard e a * trialityHadamard e b) *
          (trialityHadamard e c * trialityHadamard e d)) := by
      simp only [trialityIntegerMatrix]
      ring
    _ = 1 := by rw [hd, hh]; norm_num

private theorem ninthIntegerAbsTwoCases (a : ℤ) (ha : |a| = 2) : a = 2 ∨ a = -2 := by
  by_cases h : 0 ≤ a
  · left
    simpa only [abs_of_nonneg h] using ha
  · right
    have hn : -a = 2 := by simpa only [abs_of_neg (lt_of_not_ge h)] using ha
    omega

/-- Four integer terms of absolute value two with negative product have sum bounded by four. -/
theorem generatedNinth_four_integer_terms_abs_le (a b c d : ℤ)
    (ha : |a| = 2) (hb : |b| = 2) (hc : |c| = 2) (hd : |d| = 2)
    (hp : a * b * c * d = -16) : |a + b + c + d| ≤ 4 := by
  rcases ninthIntegerAbsTwoCases a ha with rfl | rfl <;>
    rcases ninthIntegerAbsTwoCases b hb with rfl | rfl <;>
    rcases ninthIntegerAbsTwoCases c hc with rfl | rfl <;>
    rcases ninthIntegerAbsTwoCases d hd with rfl | rfl <;> norm_num at hp <;> norm_num

/-- Two original Fourier source terms with numerator magnitude at most two have sum at most four. -/
theorem generatedNinth_octad_fourier_two_terms_abs_le (e a b : Fin 64) (x y : ℤ)
    (hx : |x| ≤ 2) (hy : |y| ≤ 2) :
    |trialityIntegerMatrix e a * x + trialityIntegerMatrix e b * y| ≤ 4 := by
  have hxa : |trialityIntegerMatrix e a * x| = |x| := by
    rw [abs_mul, generatedNinth_octad_fourier_entry_abs, one_mul]
  have hya : |trialityIntegerMatrix e b * y| = |y| := by
    rw [abs_mul, generatedNinth_octad_fourier_entry_abs, one_mul]
  calc
    _ ≤ |trialityIntegerMatrix e a * x| + |trialityIntegerMatrix e b * y| := abs_add_le _ _
    _ ≤ 4 := by rw [hxa, hya]; omega

/-- A four-term original source block with zero label XOR and negative sign product is bounded
at every Fourier row. -/
theorem generatedNinth_octad_fourier_four_terms_abs_le (e a b c d : Fin 64)
    (x y z w : ℤ) (hx : |x| = 2) (hy : |y| = 2) (hz : |z| = 2) (hw : |w| = 2)
    (hzero : trialityXor (trialityXor a b) (trialityXor c d) = 0)
    (hp : x * y * z * w = -16) :
    |trialityIntegerMatrix e a * x + trialityIntegerMatrix e b * y +
      trialityIntegerMatrix e c * z + trialityIntegerMatrix e d * w| ≤ 4 := by
  apply generatedNinth_four_integer_terms_abs_le
  · simpa only [abs_mul, generatedNinth_octad_fourier_entry_abs, one_mul] using hx
  · simpa only [abs_mul, generatedNinth_octad_fourier_entry_abs, one_mul] using hy
  · simpa only [abs_mul, generatedNinth_octad_fourier_entry_abs, one_mul] using hz
  · simpa only [abs_mul, generatedNinth_octad_fourier_entry_abs, one_mul] using hw
  · calc
      _ = (trialityIntegerMatrix e a * trialityIntegerMatrix e b *
          trialityIntegerMatrix e c * trialityIntegerMatrix e d) * (x * y * z * w) := by ring
      _ = -16 := by rw [generatedNinth_octad_fourier_four_product e a b c d hzero, hp]; norm_num

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
