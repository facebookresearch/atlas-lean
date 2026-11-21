/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Dynamics.FiniteActivePopulation.Generator

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

/-- The generator is a rate matrix for nonnegative rates. -/
example (f : ℕ → ℝ) (hf : ∀ i : Fin (2 + 1), 0 ≤ f (i : ℕ)) :
    ProbabilityTheory.IsRateMatrix (birthDeathGenerator 2 1 f) :=
  birthDeath_isRateMatrix 2 1 f zero_le_one hf

/-- Endpoint diagonals: births only at `0`, deaths only at the cap. -/
example (f : ℕ → ℝ) :
    birthDeathGenerator 2 1 f 0 0 = -((2:ℝ) * f 0) :=
  (birthDeath_endpoint_diag 2 1 f).1

end MathlibExtTest.Biology.Dynamics.FiniteActivePopulation.Generator
