/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.MixingCoefficients
import Mathlib.Probability.Distributions.Bernoulli

/-! # Bradley's inequality for repeated observations of one fair bit -/

open MeasureTheory ProbabilityTheory

namespace MetaMathlibExt.MixingCoefficientsTest

private noncomputable abbrev coin : Measure Bool :=
  bernoulliMeasure true false ⟨1 / 2, by norm_num, by norm_num⟩

-- Every positive-probability conditioning event changes a probability by at most one half.
private lemma coin_cond_bound (S T : Set Bool) (hS : coin S ≠ 0) :
    |(cond coin S T).toReal - (coin T).toReal| ≤ 1 / 2 := by
  classical
  rw [cond_apply MeasurableSet.of_discrete, ENNReal.toReal_mul, ENNReal.toReal_inv]
  change |(coin.real S)⁻¹ * coin.real (S ∩ T) - coin.real T| ≤ 1 / 2
  by_cases hs : true ∈ S <;> by_cases hs' : false ∈ S <;>
    by_cases ht : true ∈ T <;> by_cases ht' : false ∈ T <;>
    norm_num [coin, bernoulliMeasure_apply, bernoulliMeasure_real_apply, MeasurableSet.of_discrete,
      hs, hs', ht, ht', unitInterval.symm] at *

-- At lag one, both blocks observe the same bit. The bound applies even to the empty event.
example (A B : Set Bool) : |coin.real (A ∩ B) - coin.real A * coin.real B| ≤ 1 / 4 := by
  have observed {P : ℕ → Prop} (j : ℕ) (hj : P j) (E : Set Bool) :
      MeasurableSet[⨆ i, ⨆ _ : P i, Bool.instMeasurableSpace.comap id] E := by
    have hle : Bool.instMeasurableSpace.comap id ≤
        ⨆ i, ⨆ _ : P i, Bool.instMeasurableSpace.comap id :=
      le_iSup_of_le j (le_iSup_of_le hj le_rfl)
    exact hle E ⟨E, MeasurableSet.of_discrete, rfl⟩
  calc
    _ ≤ (1 / 2 : ℝ) / 2 :=
      alpha_mixing_le_half_phi_mixing coin (fun _ => id) (fun _ => measurable_id) (k := 1)
        le_rfl _ (fun _ _ S T _ _ => coin_cond_bound S T) (p := 1) le_rfl
        (observed 1 (by decide) A) (observed 2 (by decide) B)
    _ = 1 / 4 := by norm_num

-- Taking heads for both events attains the bound.
example :
    |coin.real ({true} ∩ {true}) - coin.real {true} * coin.real {true}| = 1 / 4 := by
  norm_num [coin, bernoulliMeasure_real_apply, MeasurableSet.of_discrete]

end MetaMathlibExt.MixingCoefficientsTest
