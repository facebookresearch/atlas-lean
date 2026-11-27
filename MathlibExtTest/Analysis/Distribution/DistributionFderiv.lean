/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Distribution.DistributionFderiv

open LineDeriv TopologicalSpace
open scoped Distributions
open MathlibExt.Analysis.Distribution.DistributionFderivWanted (exists_fderiv_distribution)

/-- On the Dirac mass at zero, evaluating the full derivative in direction `1` takes
minus the directional derivative of the test function at zero. -/
example : ∃ D : 𝓓'((⊤ : Opens ℝ), ℝ) →L[ℝ] (ℝ →L[ℝ] 𝓓'((⊤ : Opens ℝ), ℝ)),
    ∀ g : 𝓓((⊤ : Opens ℝ), ℝ), D (Distribution.delta 0) 1 g = -(∂_{(1 : ℝ)} g) 0 := by
  obtain ⟨D, hD⟩ := exists_fderiv_distribution (E := ℝ) (Ω := ⊤) (F := ℝ)
  refine ⟨D, fun g => ?_⟩
  rw [hD, Distribution.lineDerivOp_apply_apply, Distribution.delta_apply]
  rfl
