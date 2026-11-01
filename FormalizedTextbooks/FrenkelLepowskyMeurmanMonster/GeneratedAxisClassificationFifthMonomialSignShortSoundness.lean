/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignFourierCache
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationFifthMonomialSignFixed

/-! Ordinary soundness of integer DH and genuine preferred-Q phase certificates. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- The actual corrected integer Fourier convolution, with its common input sign omitted. -/
def generatedFifthSignShortNumerator (S C : Fin 64 → ZMod 2) (j : Fin 56) (e : Fin 64) : ℤ :=
  (if C e = 0 then 1 else -1) *
    ∑ f : Fin 64, generatedFifthSignFourierCache f e * (if S f = 0 then 1 else -1) *
      generatedFifthSignFourierCache (generatedFifthEvenRootSign j) f

private theorem matrix_real (e f : Fin 64) :
    trialityRealMatrix e f = (generatedFifthSignFourierCache e f : ℝ) / 8 := by
  rw [generatedFifth_sign_fourier_cache]
  change (1 / 8 : ℝ) * (trialityIntegerMatrix e f : ℝ) = _
  ring

private theorem phase_integer (p : ZMod 2) :
    qSign p = ((if p = 0 then 1 else -1 : ℤ) : ℝ) := by
  simp only [Int.cast_ite, Int.cast_one, Int.cast_neg, qSign]

/-- A checked full integer convolution proves genuine fixation of one actual octad coordinate. -/
theorem generatedFifth_sign_short_octad_of_certificate (k : Fin 12) (j : Fin 56) (e : Fin 64)
    (S C : Fin 64 → ZMod 2)
    (hS : ∀ f, generatedFifthSignCachedShortPhase (sourceQCode (generatedFifthSignCode k) 0)
      (Sum.inr (j, f)) = S f)
    (hC : ∀ f, generatedFifthSignCachedShortPhase (generatedFifthSignCorrection k)
      (Sum.inr (j, f)) = C f)
    (hn : generatedFifthSignShortNumerator S C j e =
      8 * generatedFifthSignFourierCache e (generatedFifthEvenRootSign j)) :
    (griessConwayEncode (rhoLocal (localFiberIntoH (generatedFifthSignCorrectedFiber k))
      generatedFifthAxis)).2.1 (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) =
        (griessConwayEncode generatedFifthAxis).2.1
          (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) := by
  rw [generatedFifthSignCorrectedFiber, map_mul, generatedFifth_sign_fiber_local, map_mul]
  change (griessConwayEncode (rhoLocal
    (localFiberIntoH (localFiberIncl (generatedFifthSignCorrection k)))
      (rhoLocal (generatedFifthSignLocal (generatedFifthSignCode k) 0)
        generatedFifthAxis))).2.1 _ = _
  rw [generatedFourth_local_short, generatedFourthQ_short_coordinate]
  have hp := generatedFifth_sign_cached_phase_actual (generatedFifthSignCorrection k)
    (Sum.inr (j, e))
  change localShortPhase (localFiberIncl (generatedFifthSignCorrection k))
    (Sum.inr (Sum.inl (generatedFifthEvenRootOctad j, e))) = _ at hp
  rw [hp, hC, generatedFifth_sign_octad_action, generatedFifth_final_octad_coordinate]
  simp_rw [hS, matrix_real]
  calc
    _ = (generatedFifthSignShortNumerator S C j e : ℝ) / 64 *
        qSign (generatedFifthEvenCoefficientPhase j) := by
      simp only [generatedFifthSignShortNumerator, Int.cast_mul, Int.cast_sum,
        Int.cast_ite, Int.cast_one, Int.cast_neg]
      simp only [qSign]
      simp_rw [Finset.mul_sum]
      simp_rw [Finset.sum_div, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro f _
      ring
    _ = _ := by rw [hn, Int.cast_mul, Int.cast_ofNat]; ring

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
