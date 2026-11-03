/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Configuration.ProductMeasure

/-!
# Tests for `MathlibExt.Probability.Configuration.ProductMeasure`

* `StatMech.bernoulliMeasure`: masses of `true` and `false` at `p = 1/3`.
* `StatMech.bernoulliProductMeasure`: on `Fin 2` with `p = 1/3`, the mass of the full
  configuration is `1/9` (`real_singleton`); the masses sum to `1` (`sum_real_singleton`);
  log-modularity (`real_singleton_logModular`) is applied to two incomparable configurations.
-/

@[expose] public section

namespace MathlibExtTest.StatMech.Probability.Configuration.ProductMeasure

open MeasureTheory NNReal
open _root_.StatMech

lemma third_le_one : (1 / 3 : ℝ≥0) ≤ 1 := by
  rw [div_le_one (by norm_num)]; norm_num

/-- `Bernoulli(1/3)` gives `true` mass `1/3` and `false` mass `2/3`. -/
example : (bernoulliMeasure (1 / 3) third_le_one).real {true} = 1 / 3 ∧
    (bernoulliMeasure (1 / 3) third_le_one).real {false} = 2 / 3 := by
  constructor
  · simp [measureReal_def]
  · rw [measureReal_def, bernoulliMeasure_apply_false, ENNReal.coe_toReal,
      NNReal.coe_sub third_le_one]
    norm_num

/-- On `Fin 2` with `p = 1/3`, the full configuration has mass `(1/3)^2 = 1/9`. -/
example : (bernoulliProductMeasure (E := Fin 2) (1 / 3) third_le_one).real {⊤} = 1 / 9 := by
  rw [bernoulliProductMeasure.real_singleton]
  simp [measureReal_def]
  norm_num

/-- The configuration masses on `Fin 2` sum to `1`. -/
example : ∑ ω : ConfigSpace (Fin 2),
    (bernoulliProductMeasure (E := Fin 2) (1 / 3) third_le_one).real {ω} = 1 :=
  bernoulliProductMeasure.sum_real_singleton

/-- Log-modularity for the incomparable configurations `![true, false]` and `![false, true]`:
`w(a) w(b) = w(⊤) w(⊥)`. -/
example : let μ := bernoulliProductMeasure (E := Fin 2) (1 / 3) third_le_one
    μ.real {![true, false]} * μ.real {![false, true]} = μ.real {⊤} * μ.real {⊥} := by
  intro μ
  have h := bernoulliProductMeasure.real_singleton_logModular (E := Fin 2) (p := 1 / 3)
    (hp := third_le_one) ![true, false] ![false, true]
  have hsup : (![true, false] ⊔ ![false, true] : ConfigSpace (Fin 2)) = ⊤ := by decide
  have hinf : (![true, false] ⊓ ![false, true] : ConfigSpace (Fin 2)) = ⊥ := by decide
  rwa [hsup, hinf] at h

/-- The product measure is a probability measure. -/
example : IsProbabilityMeasure (bernoulliProductMeasure (E := ℕ) (1 / 3) third_le_one) :=
  inferInstance

end MathlibExtTest.StatMech.Probability.Configuration.ProductMeasure
