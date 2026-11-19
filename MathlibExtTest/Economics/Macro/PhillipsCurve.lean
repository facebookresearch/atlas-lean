/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Macro.PhillipsCurve
import Mathlib.Tactic.NormNum

@[expose] public section

namespace MathlibExtTest.Economics.Macro.PhillipsCurve

open MathlibExt.Economics.Macro.PhillipsCurve

/-- Concrete disinflation: slope `κ = 1 / 2`, natural rate `5`, constant gap `2`,
so inflation falls by `1` per period: `π 1 = π 0 - 1` and `π 2 = π 0 - 2`.
Prove by applying `phillips_acceleration`. -/
theorem phillips_example {π πe u : ℕ → ℝ}
    (hexp : AdaptiveExpectations πe π) (hpc : IsPhillipsCurve π πe u (1 / 2) 5)
    (hgap : ∀ t, u (t + 1) - 5 = 2) : π 1 = π 0 - 1 ∧ π 2 = π 0 - 2 := by
  have h1 := phillips_acceleration hexp hpc hgap 1
  have h2 := phillips_acceleration hexp hpc hgap 2
  norm_num at h1 h2
  exact ⟨h1, h2⟩

/-- Concrete natural rate: if unemployment is always at the natural rate `5`, then
`π 1 = π 0`. Prove by applying `phillips_natural_rate`. -/
theorem phillips_natural_example {π πe u : ℕ → ℝ}
    (hexp : AdaptiveExpectations πe π) (hpc : IsPhillipsCurve π πe u (1 / 2) 5)
    (hnat : ∀ t, u t = 5) : π 1 = π 0 := by
  exact phillips_natural_rate hexp hpc hnat 0

end MathlibExtTest.Economics.Macro.PhillipsCurve
