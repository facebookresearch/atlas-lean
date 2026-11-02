/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import CSLibExt.Complexity.BooleanFunctions.KKL.VarGapImplications
public import CSLibExtTest.Complexity.BooleanFunctions.KKL.BKKKLLevel2

/-!
# Tests for the variance-gap core

Tests for `CSLibExt.Complexity.BooleanFunctions.KKL.VarGapImplications`:

* the hypothesis `maxInfl = 0` of `vgc_totalInfl_zero_of_maxInfl_zero` and
  `vgc_var_zero_of_maxInfl_zero` is proved for the constant-false function on two
  variables, and both conclusions are derived from it;
* `vgc_varPowerCore_c0` at `p = 1/2`, `u = 1/2` on two variables;
* `vgc_poincare_is_delta0_instance` on the one-variable dictator (`p(1-p) ≤ p(1-p)`) and
  `vgc_gap_vanishes_at_p_half`.

Window predicate: `vgc_VarPowerCore q` is refuted for every `q > 1/2`
(`vgp_varPowerCore_refutable`, tested at `q = 1`; also `ctc_varPowerCore_false` for
`q > 3/4`). No chain is run from it.
-/

@[expose] public section

namespace StatMechTest.BooleanFunctions.VarGapImplications

open Finset StatMech StatMech.OSSS StatMech.Probability
open StatMechTest.BooleanFunctions.BKKKLLevel2 (maxInfl_constFalse)

example : totalInfl (OSSS.bernoulliWeight (1 / 2))
    (fun ω => if (fun _ => false : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0) = 0 :=
  vgc_totalInfl_zero_of_maxInfl_zero (by norm_num) (by norm_num) _ (maxInfl_constFalse _)

example : OSSS.expect (OSSS.bernoulliWeight (1 / 3))
      (fun ω => if (fun _ => false : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0)
    * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 3))
      (fun ω => if (fun _ => false : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0)) = 0 :=
  vgc_var_zero_of_maxInfl_zero (by norm_num) (by norm_num) _ (maxInfl_constFalse _)

example : OSSS.expect (OSSS.bernoulliWeight (1 / 2))
      (fun ω => if (fun _ => false : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0)
    * (1 - OSSS.expect (OSSS.bernoulliWeight (1 / 2))
      (fun ω => if (fun _ => false : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0))
    ≤ ((1 / 2) / (4 + 2 * (1 / 2)))
      * ((ptn_sigma (1 / 2)) ^ 2
        * ((maxInfl (OSSS.bernoulliWeight (1 / 2))
            (fun ω => if (fun _ => false : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0))
            ^ ((1 / 2 : ℝ) / (2 - 1 / 2))
          * totalInfl (OSSS.bernoulliWeight (1 / 2))
            (fun ω => if (fun _ => false : ConfigSpace (Fin 2) → Bool) ω then (1 : ℝ) else 0))) :=
  vgc_varPowerCore_c0 (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- `vgc_poincare_is_delta0_instance` on the dictator: `p(1-p) ≤ p(1-p) · 1`. -/
example {p : ℝ} (hp0 : 0 < p) (hp1 : p < 1) : p * (1 - p) ≤ p * (1 - p) * 1 := by
  have h := vgc_poincare_is_delta0_instance hp0 hp1 (fun ω : ConfigSpace (Fin 1) => ω 0)
  rwa [vgp_dictator_meanVar hp0 hp1, vgp_dictator_totalInfl hp0 hp1, ptn_sigma_sq hp0 hp1] at h

example : (1 - (2 / 3 : ℝ)) ^ (4 - 1) - ((1 - 2 / 3) * (4 * (1 / 2 : ℝ) * (1 - 1 / 2))) ^ (4 - 1)
    = 0 :=
  vgc_gap_vanishes_at_p_half 4

example : ¬ vgc_VarPowerCore 1 := vgp_varPowerCore_refutable (by norm_num)
example : ¬ vgc_VarPowerCore 1 := ctc_varPowerCore_false (by norm_num)

end StatMechTest.BooleanFunctions.VarGapImplications
