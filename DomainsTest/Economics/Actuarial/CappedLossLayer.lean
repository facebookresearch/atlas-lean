/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Economics.Actuarial.CappedLossLayer
import Mathlib.Probability.Distributions.Bernoulli
import Mathlib.Tactic.NormNum

/-! # Tests for the deductible, limit and coinsurance layer -/

namespace DomainsTest.Economics.Actuarial

open Domains.Economics.Actuarial MathlibExt.Probability.Finance.OptionPayoffs
open MeasureTheory ProbabilityTheory

-- Below attachment, at attachment, inside the layer, at exhaustion and above it.
example : cededLoss 2 4 (1 / 2) 1 = 0 ∧ cededLoss 2 4 (1 / 2) 2 = 0 ∧
    cededLoss 2 4 (1 / 2) 3 = 1 / 2 ∧ cededLoss 2 4 (1 / 2) 6 = 2 ∧
    cededLoss 2 4 (1 / 2) 11 = 2 := by
  norm_num [cededLoss, europeanCallPayoff]

-- A zero deductible and the two endpoint shares need no special conventions.
example : cededLoss 0 4 0 7 = 0 ∧ cededLoss 0 4 1 3 = 3 ∧ retainedLoss 0 4 1 7 = 3 := by
  norm_num [retainedLoss, cededLoss, europeanCallPayoff]

example {d L ρ s : ℝ} (hd : 0 ≤ d) (hL : 0 < L) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hs : 0 ≤ s) :
    cededLoss d L ρ s = ρ * (europeanCallPayoff s d - europeanCallPayoff s (d + L)) ∧
    (0 ≤ cededLoss d L ρ s ∧ cededLoss d L ρ s ≤ min s (ρ * L)) ∧
    0 ≤ retainedLoss d L ρ s ∧ retainedLoss d L ρ s + cededLoss d L ρ s = s :=
  ⟨cededLoss_eq_callSpread d hL.le ρ s, cededLoss_bounds hd hL.le hρ.1 hρ.2 hs,
    retainedLoss_nonneg hd hL.le hρ.1 hρ.2 hs, retainedLoss_add_cededLoss d L ρ s⟩

-- Loss 3 with probability 1/4; loss 11 with probability 3/4.
private def loss (high : Bool) : ℝ := if high then 11 else 3

private noncomputable def quarter : unitInterval := ⟨1 / 4, by constructor <;> norm_num⟩

local notation "P" => bernoulliMeasure false true quarter

example : Integrable (fun ω ↦ cededLoss 2 4 (1 / 2) (loss ω)) P :=
  integrable_cededLoss (integrable_bernoulliMeasure _ _ _ loss) 2 (by norm_num) (1 / 2)

-- Both stop-loss expectations are calculated from this law, not assumed as moments.
example : (∫ ω, cededLoss 2 4 (1 / 2) (loss ω) ∂P) = 13 / 8 := by
  rw [integral_cededLoss (integrable_bernoulliMeasure _ _ _ loss) 2 (L := 4) (by norm_num) (1 / 2)]
  norm_num [stopLossTransform, integral_bernoulliMeasure, quarter, loss, smul_eq_mul,
    europeanCallPayoff]

-- With this same law, omitting the cap gives 7/2; moving the cap after scaling gives 25/8.
-- Both differ from the layer's 13/8 because exhaustion occurs in the high-loss state.
example : (∫ ω, (1 / 2 : ℝ) * europeanCallPayoff (loss ω) 2 ∂P) = 7 / 2 ∧
    (∫ ω, min ((1 / 2 : ℝ) * europeanCallPayoff (loss ω) 2) 4 ∂P) = 25 / 8 := by
  norm_num [integral_bernoulliMeasure, quarter, loss, smul_eq_mul, europeanCallPayoff]

end DomainsTest.Economics.Actuarial
