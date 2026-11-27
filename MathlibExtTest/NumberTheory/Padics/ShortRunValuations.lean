/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.Padics.ShortRunValuations
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Complex.ExponentialBounds

namespace MetaMathlibExt.card_max_padicValNat_add_gt_isLittleO

open Filter Finset Real Topology

private noncomputable def lengthAt (x : ℕ) : ℕ := ⌊exp (0.8 * √(log x))⌋₊

open scoped Classical in
private noncomputable def startingPoints (x : ℕ) : Finset ℕ :=
  (Icc 1 x).filter fun m => ∃ p : ℕ, p.Prime ∧ p < 2 * lengthAt x ∧
    let D : ℕ := 1 + ⌊log x / log p⌋₊
    (D : ℝ) / log D < ((Icc 1 (lengthAt x)).sup fun i => padicValNat p (m + i) : ℕ)

-- The proportion of exceptional starting points tends to zero.
example : Tendsto (fun x : ℕ => ((startingPoints x).card : ℝ) / x) atTop (𝓝 0) :=
  card_max_padicValNat_add_gt_isLittleO.tendsto_div_nhds_zero

-- At x = 1 the strict prime bound excludes 2.
example : startingPoints 1 = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro m hm
  obtain ⟨_, p, hp, hpk, _⟩ := mem_filter.mp hm
  exact hp.two_le.not_gt (by simpa [lengthAt] using hpk)

-- At x = 8 the run starting at 7 already witnesses an exception at its first shift.
example : 7 ∈ startingPoints 8 := by
  classical
  have hlog : 0 < log 2 := log_pos (by norm_num)
  have hlog8 : log 8 = 3 * log 2 := by
    convert log_pow 2 3 using 1
    norm_num
  have hK : 2 ≤ lengthAt 8 := by
    apply Nat.le_floor
    norm_num only [Nat.cast_ofNat]
    rw [← log_le_iff_le_exp (by norm_num), hlog8]
    have hsqrt : 1 ≤ √(3 * log 2) := Real.one_le_sqrt.mpr (by linarith [log_two_gt_d9])
    linarith [log_two_lt_d9]
  refine mem_filter.mpr ⟨by decide, 2, Nat.prime_two, by omega, ?_⟩
  have hD : 1 + ⌊log (8 : ℝ) / log 2⌋₊ = 4 := by
    rw [hlog8, mul_div_cancel_right₀ _ hlog.ne']
    norm_num
  dsimp only
  norm_num only [Nat.cast_ofNat]
  rw [hD]
  have hlog4 : log 4 = 2 * log 2 := by
    convert log_pow 2 2 using 1
    norm_num
  have hi : 1 ∈ Icc 1 (lengthAt 8) := mem_Icc.mpr ⟨le_rfl, by omega⟩
  have hval : 3 ≤ (Icc 1 (lengthAt 8)).sup (fun i => padicValNat 2 (7 + i)) :=
    (by decide +kernel : 3 ≤ padicValNat 2 (7 + 1)).trans
      (le_sup (f := fun i => padicValNat 2 (7 + i)) hi)
  apply lt_of_lt_of_le _ (Nat.cast_le.mpr hval : (3 : ℝ) ≤ _)
  norm_num only [Nat.cast_ofNat]
  rw [hlog4, div_lt_iff₀ (by positivity)]
  linarith [log_two_gt_d9]

end MetaMathlibExt.card_max_padicValNat_add_gt_isLittleO
