/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.FSRhoOptimise
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.KKLInequality

/-!
# Tests for the KKL inequality at `p = 1/2`

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.FSRhoOptimise`:

* the headline `fsr_pbiased_endpoint : KKLHypercontractive (1/2) 2`, combined with
  `kkl_inequality_total` and `kkl_inequality_max`, gives for the `AND` function on `{0, 1}^Bool`
  the explicit inequality `2 · 3/16 · log 2 ≤ 1`, with a nonzero logarithmic factor;
* together with the refutation of `KKLHypercontractive (1/2) 8` (test file for
  `KKL.KKLInequality`), this shows the proved constant `2` lies in the range where the predicate
  has content;
* the `p = 1/2` identities `fsr_ptn_psi_half`, `fsr_ptn_pchar_half`, `fsr_ptn_coeff_half_sq` and
  `fsr_totalInfl_half_eq` at small inputs.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions

open StatMech StatMech.OSSS StatMech.Probability

/-- The headline at `AND`: `2 · Var · log (1 / maxInf) ≤ totalInf` is `3/8 · log 2 ≤ 1`. -/
example : 2 * (3 / 16) * Real.log 2 ≤ 1 := kkl_at_andFun fsr_pbiased_endpoint

/-- The logarithmic factor in the headline at `AND` is positive, so the instance is not trivial. -/
example : 0 < 2 * var νHalf andInd * Real.log (1 / maxInfl νHalf andInd) := by
  rw [var_andFun, maxInfl_andInd]
  have := Real.log_pos (show (1 : ℝ) < 1 / (1 / 2) by norm_num)
  positivity

/-- Maximal-influence form at `AND`. -/
example : 2 * var νHalf andInd * Real.log (1 / maxInfl νHalf andInd)
    ≤ (Fintype.card Bool : ℝ) * maxInfl νHalf andInd :=
  kkl_inequality_max fsr_pbiased_endpoint andFun

/-- The headline applies to Boolean functions on any finite nonempty index type. -/
example (φ : ConfigSpace (Fin 5) → Bool) :
    2 * var (bernoulliWeight (1 / 2)) (fun ω => if φ ω then (1 : ℝ) else 0)
        * Real.log (1 / maxInfl (bernoulliWeight (1 / 2)) (fun ω => if φ ω then (1 : ℝ) else 0))
      ≤ totalInfl (bernoulliWeight (1 / 2)) (fun ω => if φ ω then (1 : ℝ) else 0) :=
  kkl_inequality_total fsr_pbiased_endpoint φ

/-! ## The `p`-biased basis at `p = 1/2` -/

example : ptn_psi (1 / 2 : ℝ) true = 1 ∧ ptn_psi (1 / 2 : ℝ) false = -1 := by
  rw [fsr_ptn_psi_half, fsr_ptn_psi_half]; simp

example (ω : ConfigSpace Bool) :
    ptn_pchar (1 / 2 : ℝ) {true} ω = -khc_walshChar {true} ω := by
  rw [fsr_ptn_pchar_half]; simp

/-- The top `p`-biased coefficient of `AND` at `p = 1/2` is `1/4`. -/
lemma ptn_coeff_half_andInd_univ : ptn_coeff (1 / 2 : ℝ) andInd Finset.univ = 1 / 4 := by
  unfold ptn_coeff ptn_pchar
  simp only [fsr_ptn_psi_half]
  simp [expect, weight, sum_configSpace_bool, andFun, bernoulliWeight]
  norm_num

example : (khc_fourierCoeff andInd Finset.univ) ^ 2 = 1 / 16 := by
  rw [← fsr_ptn_coeff_half_sq, ptn_coeff_half_andInd_univ]; norm_num

example : ∑ S : Finset Bool, 4 * (S.card : ℝ) * (ptn_coeff (1 / 2 : ℝ) andInd S) ^ 2 = 1 := by
  rw [← fsr_totalInfl_half_eq, totalInfl_andInd]

end StatMechTest.BooleanFunctions
