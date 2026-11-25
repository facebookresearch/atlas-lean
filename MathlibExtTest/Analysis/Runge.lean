/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Runge

open Metric Polynomial Set
open scoped Polynomial

-- The unit circle surrounds a pole of the function, while its open neighborhood omits the pole.
example (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ sphere (0 : ℂ) 1, q.eval z ≠ 0) ∧
      ∀ z ∈ sphere (0 : ℂ) 1, ‖z⁻¹ - p.eval z / q.eval z‖ < ε := by
  apply MathlibExt.Analysis.RungeWanted.ComplexAnalysis.runge
    (sphere 0 1) (isCompact_sphere _ _) ({0}ᶜ) isOpen_compl_singleton _ (fun z ↦ z⁻¹) _ ε hε
  · rintro z hz rfl
    simp at hz
  · intro z hz
    exact analyticAt_id.inv hz
