/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.RogersDilogLucasUSeries

/-! # The Lucas sequence $U(3, 1)$ at $k = 1$ -/

open Real

namespace MathlibExtTest.RogersDilogLucasUSeries

/-- The parameters $(P, Q) = (3, 1)$, with $D = 5 > 0$. -/
private def params : MetaMathlibExt.LucasSequenceParams :=
  ⟨3, 1, by norm_num⟩

example :
    let L (x : ℝ) := (∑' n : ℕ, x ^ (n + 1) / ((n : ℝ) + 1) ^ 2) + log x * log (1 - x) / 2
    ∑' n : ℕ, L (1 / (MetaMathlibExt.lucasU params (n + 2) : ℝ) ^ 2) =
      L (1 / (((3 : ℝ) + √5) / 2) ^ 2) := by
  intro L
  have h := MetaMathlibExt.rogersDilog_lucasU_series params (by decide) (by decide)
    (by decide) (k := 1) (by norm_num)
  have hα : (((params.p : ℤ) : ℝ) + √(((params.p ^ 2 - 4 * params.q : ℤ) : ℝ))) / 2 =
      ((3 : ℝ) + √5) / 2 := by
    simp [params]
  rw [hα] at h
  simpa [L, params, MetaMathlibExt.lucasU] using h

end MathlibExtTest.RogersDilogLucasUSeries
