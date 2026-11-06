/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import
  FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsSignTensorYPhase

/-! Physical tensor coordinate units as exact two-term original Y/Z dictionary packets. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- A single actual physical tensor coordinate. -/
def generatedAxisGlobalTensorUnit (t : SpinIndex) (i : Fin 24) :
    SpinIndex → Fin 24 → ℝ :=
  fun u j => if u = t then if j = i then 1 else 0 else 0

/-- Every physical tensor unit has its exact two-term original dictionary expansion. -/
theorem generatedAxisGlobalTensorUnit_dictionary (d : Fin 2048) (b : ZMod 2) (i : Fin 24) :
    Real.sqrt 2 • generatedAxisGlobalTensorUnit
      (generatedFifthSpinLow d + b • (Pi.single 11 1 : SpinIndex)) i =
    (qSign b * (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1)) •
      trialityYTensor d i +
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) • trialityZTensor d i := by
  have hs : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hn : Real.sqrt 2 ≠ 0 := by positivity
  have hp := qSign_sq (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ)
  funext t j
  change Real.sqrt 2 * (if t = generatedFifthSpinLow d +
      b • (Pi.single 11 1 : SpinIndex) then if j = i then 1 else 0 else 0) =
    (qSign b * (if (golayEncodedMask d.val).testBit i.val then (-1 : ℝ) else 1)) *
      trialityYTensor d i t j +
      qSign (golayMaskWeight (golayEncodedMask d.val) / 4 : ℕ) * trialityZTensor d i t j
  rw [trialityYTensor, trialityZTensor]
  by_cases hj : j = i
  · subst j
    by_cases hd : spinDictionaryCode t = d
    · obtain ⟨c, hc⟩ := (generatedFifth_sign_dictionary_eq t d).mp hd
      have ht : t 11 = c := by
        rw [hc]
        simp only [Pi.add_apply, generatedFifth_spin_low_last, Pi.smul_apply,
          Pi.single_apply, ite_true, smul_eq_mul, mul_one, zero_add]
      have he : t = generatedFifthSpinLow d + b • (Pi.single 11 1 : SpinIndex) ↔ c = b := by
        constructor
        · intro h
          have hh := congrFun h 11
          simpa only [ht, Pi.add_apply, generatedFifth_spin_low_last, Pi.smul_apply,
            Pi.single_apply, ite_true, smul_eq_mul, mul_one, zero_add] using hh
        · intro h
          simpa only [h] using hc
      have bits (a : ZMod 2) : a = 0 ∨ a = 1 := by fin_cases a <;> simp
      rcases bits b with rfl | rfl <;> rcases bits c with rfl | rfl <;>
        cases hf : (golayEncodedMask d.val).testBit i.val
      all_goals simp only [he, hd, ht]
      all_goals norm_num
      all_goals field_simp
      all_goals nlinarith [hs, hp]
    · have he : t ≠ generatedFifthSpinLow d + b • (Pi.single 11 1 : SpinIndex) := by
        intro h
        exact hd ((generatedFifth_sign_dictionary_eq t d).mpr ⟨b, h⟩)
      simp [he, hd]
  · simp [hj]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
