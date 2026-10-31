/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABMeanfieldLimit

/-!
# Tests for `PhyslibExt.CondensedMatter.IsingModel.Sharpness.ABMeanfieldLimit`

* `abml_meanfield_limit` on the constant sequence `M_n = M = 1` at `β = 1` (hypotheses
  satisfiable, conclusion `0 ≤ 0`);
* `abml_meanfield_limit` on the identity sequence `M_n b = b` at `β = 1`, where `1 - b ≤ b` for
  `b ≥ 1`.
-/

@[expose] public section

namespace PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABMeanfieldLimit

open _root_.StatMech _root_.StatMech.Sharpness

-- Constant magnetizations.
example : 1 - (fun _ : ℝ => (1 : ℝ)) 1 ≤ 1 * deriv (fun _ : ℝ => (1 : ℝ)) 1 :=
  abml_meanfield_limit (fun _ _ => 1) (fun _ => 1) 1 one_pos (fun _ _ _ => by simp)
    (fun _ _ => differentiableAt_const _) (fun _ _ => tendsto_const_nhds) (differentiableAt_const _)

-- The identity sequence: `1 - b ≤ b · 1` for `b ≥ 1`.
example : 1 - (fun b : ℝ => b) 1 ≤ 1 * deriv (fun b : ℝ => b) 1 :=
  abml_meanfield_limit (fun _ b => b) (fun b => b) 1 one_pos
    (fun _ b hb => by simp only [deriv_id'', mul_one]; linarith)
    (fun _ _ => differentiableAt_id) (fun _ _ => tendsto_const_nhds) differentiableAt_id

end PhyslibExtTest.CondensedMatter.IsingModel.Sharpness.ABMeanfieldLimit
