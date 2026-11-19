/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.Electronics.IdealPhotonCountingCurrent
import Mathlib.Tactic.NormNum

@[expose] public section

open PhyslibExt.Electronics.IdealPhotonCountingCurrent
open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace PhyslibExtTest.Electronics.IdealPhotonCountingCurrent

/-- Responsivity times power is charge times arrival rate. -/
example : responsivity 1 2 1 1 * 5 = |2| * photonArrivalRate 1 5 1 1 :=
  responsivity_mul_power_eq 1 5 2 1 1

/-- Mean current on the counting space itself, with the Poisson
mean discharged from the canonical MathlibExt lemma. -/
example : ∫ n, countCurrent 1 1 n ∂(poissonMeasure (photonCountMean 1 5 1 1 1))
    = responsivity 1 1 1 1 * 5 := by
  have hN : HasLaw (fun n : ℕ => n) (poissonMeasure (photonCountMean 1 5 1 1 1))
      (poissonMeasure (photonCountMean 1 5 1 1 1)) := ⟨by fun_prop, by simp⟩
  exact integral_countCurrent_eq_responsivity_mul_power ℕ _ (fun n => n)
    1 5 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hN

/-- Variance on the counting space itself, discharged. -/
example : Var[fun n => countCurrent 1 1 n; poissonMeasure (photonCountMean 1 5 1 1 1)]
    = 1 ^ 2 * photonArrivalRate 1 5 1 1 / 1 := by
  have hN : HasLaw (fun n : ℕ => n) (poissonMeasure (photonCountMean 1 5 1 1 1))
      (poissonMeasure (photonCountMean 1 5 1 1 1)) := ⟨by fun_prop, by simp⟩
  exact variance_countCurrent_eq_sq_charge_mul_rate_div ℕ _ (fun n => n)
    1 5 1 1 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hN

/-- Negative-power diagnostic (a deliberately violated premise,
kept out of the production API): with `P = -1` the nonnegative
Poisson mean clamps to `0`, so the mean current is `0`, not
`R P = -1`. -/
example : ∫ n, countCurrent 1 1 n ∂(poissonMeasure (photonCountMean 1 (-1) 1 1 1))
    ≠ responsivity 1 1 1 1 * (-1) := by
  have hclamp : photonCountMean 1 (-1) 1 1 1 = 0 := by
    unfold photonCountMean photonArrivalRate
    norm_num
  rw [hclamp]
  have hInt : (∫ n, countCurrent 1 1 n ∂(poissonMeasure 0)) = 0 := by
    have h := ProbabilityTheory.integral_natCast_poissonMeasure (0 : ℝ≥0)
    simpa [countCurrent] using h
  rw [hInt]
  norm_num [responsivity, photonArrivalRate]

end PhyslibExtTest.Electronics.IdealPhotonCountingCurrent
