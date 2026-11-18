/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Biology.Dynamics.FiniteActivePopulation.Generator

/-! Tests: endpoint rates vanish. -/

namespace MathlibExtTest.Biology.Dynamics.FiniteActivePopulation.Generator

open MathlibExt.Biology.Dynamics.FiniteActivePopulation.Generator

/-- No death at zero and no birth at the cap. -/
example : (1:ℝ) * (0:ℝ) = 0 ∧ ((5:ℝ) - 5) * (fun _ => (2:ℝ)) 5 = 0 :=
  birthDeath_endpoints 5 1 (fun _ => 2)

/-- Two-state regression: the death entry `Q 1 0` is `alpha`, not
shadowed by modular successor arithmetic. -/
example (alpha : ℝ) (f : ℕ → ℝ) :
    birthDeathGenerator 1 alpha f 1 0 = alpha := by
  simp [birthDeathGenerator]

end MathlibExtTest.Biology.Dynamics.FiniteActivePopulation.Generator
