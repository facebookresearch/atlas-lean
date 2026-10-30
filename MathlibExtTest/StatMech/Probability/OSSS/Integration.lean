/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.OSSS.Integration
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.OSSS.Integration`

* `logStep_le` at `S = 1`, `f = 1`; `slope_ge_of_deriv_ge` for `T = id`.
* `integrated_meanField` for the model `f_0 = 1`, `f_i = 0` (`i ≥ 1`), `Σ_i = 1`, where every
  hypothesis holds (with `m = 0`).
* `meanField_limit` and `meanField_lower` for `T n x = x`, `m_n = 1`.
-/

@[expose] public section

open StatMech.OSSS.Integration

namespace MathlibExtTest.StatMech.Probability.OSSS.Integration

example : Real.log (1 + 1) - Real.log 1 ≤ 1 / 1 := logStep_le 1 1 one_pos zero_le_one

example : (1 : ℝ) * (2 - 0) ≤ id 2 - id 0 :=
  slope_ge_of_deriv_ge 0 2 1 (by norm_num) id (fun _ => 1) (fun x _ => hasDerivAt_id x)
    (fun _ _ => le_rfl)

example : (2 - 1) * (0 : ℝ) ≤ meanLogTerm (fun _ _ => 0) 2 2 - meanLogTerm (fun _ _ => 0) 2 1 :=
  integrated_meanField (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 1) 2 1 2 0 (by norm_num)
    (Real.log_pos (by norm_num)) (fun _ _ _ => hasDerivAt_const _ _) (fun _ _ => by ring)
    (fun _ _ _ _ => le_rfl) (fun _ _ _ _ => one_pos) (fun _ _ _ _ => by simp)
    (fun _ _ => by simp)

example : ((2 : ℝ) - 1) * 1 ≤ 2 - 1 :=
  meanField_limit (fun _ x => x) (fun _ => 1) 1 2 2 1 1 tendsto_const_nhds tendsto_const_nhds
    tendsto_const_nhds (Filter.Eventually.of_forall fun _ => by norm_num)

example : (2 : ℝ) - 1 ≤ 2 - 1 :=
  meanField_lower (fun _ x => x) (fun _ => 1) 1 2 2 1 1 (by norm_num) le_rfl tendsto_const_nhds
    tendsto_const_nhds tendsto_const_nhds (Filter.Eventually.of_forall fun _ => by norm_num)

end MathlibExtTest.StatMech.Probability.OSSS.Integration
