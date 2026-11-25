/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.InformationTheory.ChannelCodingWeakConverse

/-!
# Weak converse for a constant channel

The channel with one possible input always emits `false`. Its capacity is zero, and a
two-message code of blocklength one has average error probability `1 / 2`: the first message is
always decoded correctly and the second always wrongly. The weak converse then says
`(1 - 1 / 2) log₂ 2 ≤ h(1 / 2)`, that is `1 / 2 ≤ 1`.
-/

open MeasureTheory InformationTheory MathlibExt.InformationTheory.ChannelCodingWanted

namespace MathlibExtTest.InformationTheory.ChannelCodingWeakConverse

private noncomputable def constantChannel (_ : Unit) : PMF Bool := PMF.pure false

private theorem capacity_zero :
    (⨆ p : PMF Unit, finiteMutualInformation
      (p.bind fun a => (constantChannel a).map (Prod.mk a))) = 0 := by
  have hp (p : PMF Unit) : p = PMF.pure () := by
    ext a
    cases a
    simpa [PMF.pure_apply] using p.tsum_coe
  have h (p : PMF Unit) : finiteMutualInformation
      (p.bind fun a => (constantChannel a).map (Prod.mk a)) = 0 := by
    rw [hp p]
    simp [constantChannel, PMF.pure_map, finiteMutualInformation_eq]
  simp_rw [h]
  simp

private theorem average_error_half :
    (∑ m : Fin 2, (Measure.pi fun _ : Fin 1 => (constantChannel ()).toMeasure).real
      {_y | (0 : Fin 2) ≠ m}) / ((2 : ℕ) : ℝ) = 1 / 2 := by
  rw [Fin.sum_univ_two]
  have h0 : {y : Fin 1 → Bool | (0 : Fin 2) ≠ 0} = ∅ := by
    ext _
    simp
  have h1 : {y : Fin 1 → Bool | (0 : Fin 2) ≠ 1} = Set.univ := by
    ext _
    simp only [Set.mem_ofPred_eq, Set.mem_univ]
    decide
  rw [h0, h1, measureReal_empty,
    show (Measure.pi fun _ : Fin 1 => (constantChannel ()).toMeasure).real Set.univ = 1 from by
      rw [measureReal_def, measure_univ, ENNReal.toReal_one]]
  norm_num

example : (1 - (1 / 2 : ℝ)) * Real.logb 2 2 ≤
    1 * (⨆ p : PMF Unit, finiteMutualInformation
      (p.bind fun a => (constantChannel a).map (Prod.mk a))) +
        Real.binEntropy (1 / 2) / Real.log 2 := by
  rw [capacity_zero]
  have h := channelCoding_weak_converse constantChannel 1 2 (by norm_num)
    (fun _ _ => ()) (fun _ => 0)
  dsimp only at h
  rw [average_error_half, capacity_zero] at h
  simpa using h

end MathlibExtTest.InformationTheory.ChannelCodingWeakConverse
