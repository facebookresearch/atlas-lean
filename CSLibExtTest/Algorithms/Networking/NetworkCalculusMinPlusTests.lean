/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Networking.NetworkCalculusMinPlus

/-! # Endpoint, signed-value and domain tests for extended min-plus operators -/

namespace Cslib.Algorithms.Networking.NetworkCalculus

open scoped NNReal ENNReal
open ExtendedCurve

-- The jump is taken *at* the threshold. Height may be infinite.
private noncomputable def jump (a : ℝ≥0) (v : ℝ≥0∞) : ExtendedCurve where
  toOrderHom := {
    toFun := fun t => if (a : ℝ) ≤ t then v else 0
    monotone' := by
      intro s t hst
      by_cases hs : (a : ℝ) ≤ s
      · simp [hs, hs.trans hst]
      · simp [hs] }
  zero_of_neg ht := ite_eq_right (not_le_of_gt (lt_of_lt_of_le ht a.2))

private theorem jump_apply (a : ℝ≥0) (v : ℝ≥0∞) (t : ℝ) :
    jump a v t = if (a : ℝ) ≤ t then v else 0 := rfl

private noncomputable def zeroCurve := jump 0 0
private noncomputable def oneAfterZero := jump 0 1
private noncomputable def twoAfterOne := jump 1 2
private noncomputable def epsilon := jump 0 ⊤

private theorem zeroCurve_apply (t : ℝ) : zeroCurve t = 0 := by
  rw [zeroCurve, jump_apply]
  split <;> rfl

-- Infinite and nonzero finite endpoint values are legal. The empty negative-time
-- interval does not set the convolution to the infimum of the empty family.
example {t : ℝ} (ht : 0 ≤ t) : epsilon t = ⊤ := by simp [epsilon, jump_apply, ht]

example {t : ℝ} (ht : t < 0) : epsilon t = 0 := epsilon.zero_of_neg ht

example (f g : ExtendedCurve) : f.conv g 0 = f 0 + g 0 := conv_zero f g

example : oneAfterZero.conv oneAfterZero 0 = 2 := by norm_num [oneAfterZero, jump_apply]

example : epsilon.conv zeroCurve 0 = ⊤ := by simp [epsilon, jump_apply, zeroCurve_apply]

example (f g : ExtendedCurve) {t : ℝ} (ht : t < 0) : f.conv g t = 0 :=
  (f.conv g).zero_of_neg ht

example (f g : ExtendedCurve) {s t : ℝ} (hst : s ≤ t) : f.conv g s ≤ f.conv g t :=
  (f.conv g).toOrderHom.monotone hst

example (t : ℝ≥0) : (ofNNReal (fun _ => 1) monotone_const).conv
    (ofNNReal (fun _ => 2) monotone_const) t = minPlusConv (fun _ => 1) (fun _ => 2) t :=
  conv_ofNNReal _ _ _ _ t

-- Ordinary signed subtraction: not the zero one would obtain by truncation.
private theorem zeroOne_admissible (t : ℝ) : t ∈ zeroCurve.deconvDomain oneAfterZero := by
  intro u
  simp [zeroCurve_apply]

example (t : ℝ) : zeroCurve.deconv oneAfterZero ⟨t, zeroOne_admissible t⟩ = -1 := by
  unfold deconv
  simp [zeroCurve_apply, oneAfterZero, jump_apply]

-- Positive output at *negative* time is a separate failure of closure. Shift 2
-- reaches the high side of the jump when the evaluation time is -1.
private theorem stepZero_admissible (t : ℝ) : t ∈ twoAfterOne.deconvDomain zeroCurve := by
  intro u
  simp [zeroCurve_apply]

example : twoAfterOne.deconv zeroCurve ⟨-1, stepZero_admissible (-1)⟩ = 2 := by
  apply le_antisymm
  · apply (deconv_le_iff ..).2
    intro u
    simp only [zeroCurve_apply, EReal.coe_ennreal_zero, sub_zero, twoAfterOne, jump_apply]
    split
    · exact le_rfl
    · norm_num
  · have h := le_deconv twoAfterOne zeroCurve ⟨-1, stepZero_admissible (-1)⟩ 2
    norm_num [twoAfterOne, jump_apply, zeroCurve_apply, ENNReal.toEReal_ofNat] at h
    exact h

-- Reject a time even if only a later shift encounters simultaneous infinity.
example : (-1 : ℝ) ∉ epsilon.deconvDomain epsilon := by
  intro h
  have h₁ := h (1 : ℝ≥0)
  norm_num [epsilon, jump_apply] at h₁

-- In contrast, either side alone can be infinite, with opposite signed results.
example (t : ℝ) : t ∈ zeroCurve.deconvDomain epsilon := fun u => by simp [zeroCurve_apply]

example (t : zeroCurve.deconvDomain epsilon) : zeroCurve.deconv epsilon t = ⊥ := by
  simp [deconv, zeroCurve_apply, epsilon, jump_apply]

example : epsilon.deconv zeroCurve ⟨0, fun u => by simp [zeroCurve_apply]⟩ = ⊤ := by
  apply top_unique
  have h := le_deconv epsilon zeroCurve ⟨0, fun u => by simp [zeroCurve_apply]⟩ 0
  simpa [epsilon, jump_apply, zeroCurve_apply] using h

end Cslib.Algorithms.Networking.NetworkCalculus
