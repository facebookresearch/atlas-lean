/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Crypto.Privacy.Transfer
import Mathlib.Probability.Distributions.Bernoulli

/-!
# Tests for the transfer theorem

Apply the theorem to a query selected by an independent fair bit and to the empty dataset.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace Cslib.Crypto.Privacy.TransferTests

private noncomputable def fairBit : Measure Bool :=
  bernoulliMeasure true false ⟨1 / 2, by constructor <;> norm_num⟩

private instance fairBit_isProbabilityMeasure : IsProbabilityMeasure fairBit := by
  unfold fairBit
  infer_instance

private noncomputable def matchQuery (q z : Bool) : ℝ := if q = z then 1 else 0

private theorem fairBit_kernel_private {n : ℕ} :
    DifferentiallyPrivate hammingAdj
      (fun S ↦ Kernel.const (Fin n → Bool) fairBit S) 0 0 := by
  intro x y _ s _
  simp

/-- An independent fair bit selects which value's sample frequency to estimate. -/
example :
    ((Measure.pi fun _ : Fin 576 ↦ fairBit) ⊗ₘ Kernel.const (Fin 576 → Bool) fairBit)
      {p | (1 / 4 : ℝ) <
        |∫ z, matchQuery p.2 z ∂fairBit - (1 / ((576 : ℕ) : ℝ)) * ∑ i, matchQuery p.2 (p.1 i)|} ≤
      ENNReal.ofReal (1 / 2) := by
  have hlog₂ : Real.log 2 ≤ 1 := calc
    _ ≤ 2 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
    _ = _ := by norm_num
  have hlog : Real.log 8 ≤ 3 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith
  refine differentiallyPrivate_transfer (P := fairBit) (β := 1 / 2) (τ := 1 / 4)
    (Kernel.const (Fin 576 → Bool) fairBit) matchQuery (measurable_of_countable _) ?_
    (by norm_num) (by norm_num) ?_ le_rfl (by norm_num) fairBit_kernel_private
  · intro q z
    unfold matchQuery
    split_ifs <;> constructor <;> norm_num
  · norm_num
    linarith

/-- With no rows the sample-size hypothesis still admits `β = 4`. -/
example :
    ((Measure.pi fun _ : Fin 0 ↦ fairBit) ⊗ₘ Kernel.const (Fin 0 → Bool) fairBit)
      {_p | (1 / 4 : ℝ) <
        |∫ _, (1 : ℝ) ∂fairBit - (1 / ((0 : ℕ) : ℝ)) * ∑ _i : Fin 0, (1 : ℝ)|} ≤
      ENNReal.ofReal 4 := by
  exact differentiallyPrivate_transfer (P := fairBit) (β := 4) (τ := 1 / 4)
    (Kernel.const (Fin 0 → Bool) fairBit) (fun _ _ ↦ 1) measurable_const
    (fun _ _ ↦ ⟨zero_le_one, le_rfl⟩) (by norm_num) (by norm_num) (by norm_num)
    le_rfl (by norm_num) fairBit_kernel_private

end Cslib.Crypto.Privacy.TransferTests
