/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.MoneyGrowthInflation

import Mathlib.Tactic

/-!
# Tests for the inflation–money-growth relation

Exact form: `M₀ = 100, M₁ = 110, Y₀ = 50, Y₁ = 55, V = 2` gives
`P₀ = P₁ = 4`, so `P₁/P₀ = 1`. Log-differenced form: affine paths
`M s = 100 + 2 * s`, `Y s = 50 + s`, constant `P s = 4`, `V = 2` at `t = 0`.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Macro.MoneyGrowthInflation

open MathlibExt.Economics.Macro.MoneyGrowthInflation

-- Test (1): exact form with M0=100, M1=110, Y0=50, Y1=55, V=2, P0=4, P1=4
example : (4 : ℝ) / 4 = 1 := by
  have h0 : (100 : ℝ) * 2 = 4 * 50 := by norm_num
  have h1 : (110 : ℝ) * 2 = 4 * 55 := by norm_num
  have h := inflation_exact h0 h1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  rw [h]
  norm_num

-- Test (2): log-differenced form, M s = 100+2*s, Y s = 50+s, P s = 4, V = 2, t = 0
example : logDeriv (fun _ : ℝ => (4:ℝ)) (0 : ℝ)
    = logDeriv (fun s : ℝ => 100 + 2*s) (0 : ℝ) - logDeriv (fun s : ℝ => 50 + s) (0 : ℝ) := by
  have hMV : ∀ s : ℝ, (100 + 2*s) * 2 = (4:ℝ) * (50 + s) := fun s => by ring
  have hM : HasDerivAt (fun s : ℝ => 100 + 2*s) 2 0 := by
    simpa using ((hasDerivAt_id (0:ℝ)).const_mul (2:ℝ)).const_add (100:ℝ)
  have hP : HasDerivAt (fun _ : ℝ => (4:ℝ)) 0 0 :=
    hasDerivAt_const (0:ℝ) (4:ℝ)
  have hY : HasDerivAt (fun s : ℝ => 50 + s) 1 0 := by
    simpa using (hasDerivAt_id (0:ℝ)).const_add (50:ℝ)
  exact inflation_logDiff hMV (by norm_num) hM hP hY (by norm_num) (by norm_num) (by norm_num)

end MathlibExtTest.Economics.Macro.MoneyGrowthInflation
