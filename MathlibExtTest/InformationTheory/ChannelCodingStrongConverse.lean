/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.InformationTheory.ChannelCodingStrongConverse

/-!
# Strong converse for a constant channel

The channel with one possible input always emits `false`. Its capacity is zero and the
strong converse applies at one bit per use, even with repeated codewords and an output
symbol of probability zero.
-/

open MeasureTheory InformationTheory MathlibExt.InformationTheory.ChannelCodingWanted

namespace MathlibExtTest.InformationTheory.ChannelCodingStrongConverse

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

example : ∀ᶠ n in Filter.atTop, ∀ (M : ℕ) (f : Fin M → Fin n → Unit)
    (g : (Fin n → Bool) → Fin M), (2 : ℝ) ^ n ≤ M →
      1 / 2 < (∑ m, (Measure.pi fun i => (constantChannel (f m i)).toMeasure).real
        {y | g y ≠ m}) / M := by
  have hR : (⨆ p : PMF Unit, finiteMutualInformation
      (p.bind fun a => (constantChannel a).map (Prod.mk a))) < 1 := by rw [capacity_zero]; norm_num
  simpa using channelCoding_strong_converse constantChannel hR (ε := 1 / 2) (by norm_num)

end MathlibExtTest.InformationTheory.ChannelCodingStrongConverse
