/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.LurothDiophantineApproximation

open Filter MeasureTheory MetaMathlibExt

-- The strict approximation inequality never holds for the zero function.
example : lurothWellApproximableSet (fun _ => 0) = ∅ := by
  ext x
  simp [lurothWellApproximableSet, not_lt_of_ge (abs_nonneg _)]

-- Setting the first two values to zero does not affect the lower order.
example : lowerOrderAtInfinity (fun q => if q < 2 then 0 else 1) = 0 := by
  have h : ∀ᶠ q : ℕ in atTop,
      ENNReal.ofReal (-Real.log (if q < 2 then 0 else 1) / Real.log q) = 0 := by
    filter_upwards [eventually_ge_atTop 2] with q hq
    simp [not_lt_of_ge hq]
  rw [lowerOrderAtInfinity, liminf_congr h, liminf_const]

-- The counterexample includes the endpoint of order zero.
example : ∃ ψ : ℕ → ℝ, (∀ q, 0 < ψ q ∧ ψ q ≤ 1) ∧
    (¬ ∃ N, AntitoneOn ψ (Set.Ici N)) ∧
    lowerOrderAtInfinity ψ = 0 ∧ dimH (lurothWellApproximableSet ψ) = 0 := by
  simpa using exists_not_antitone_dimH_lurothWellApproximableSet_eq_zero 0 (hτ := le_rfl)
