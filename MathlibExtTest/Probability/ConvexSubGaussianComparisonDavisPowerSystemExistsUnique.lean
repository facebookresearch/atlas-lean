/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.ConvexSubGaussianComparisonDavisPowerSystemExistsUnique

/-! # Tests for `MathlibExt.Probability.ConvexSubGaussianComparisonDavisPowerSystemExistsUnique` -/

open ProbabilityTheory
open MathlibExt.Probability.ConvexSubGaussianComparisonWanted
open MathlibExt.Probability.ConvexSubGaussianComparisonWantedDavis

namespace MathlibExtTest.Probability.ConvexSubGaussianComparisonDavisPowerSystemExistsUnique

-- Any two valid solutions of the Davis–Power system are equal.
example (q r : DavisPowerSolution) (hq : q.IsValid) (hr : r.IsValid) : q = r := by
  obtain ⟨w, _, huniq⟩ := davisPowerSystem_existsUnique
  rw [huniq q hq, huniq r hr]

-- The threshold equation `h a = B` has a solution above `t_0`.
example : ∃ a : ℝ, davisPowerT0 < a ∧ davisPowerH a = davisPowerB := by
  obtain ⟨q, hq, _⟩ := davisPowerSystem_existsUnique
  exact ⟨q.a, hq.1, hq.2.1⟩

-- The `p_0` of a solution lies strictly between zero and one and is a value of `Q`.
example : ∃ p : ℝ, 0 < p ∧ p < 1 ∧ ∃ z : ℝ, standardNormalTail z = p := by
  obtain ⟨q, hq, _⟩ := davisPowerSystem_existsUnique
  exact ⟨q.p0, hq.2.2.2.1, hq.2.2.2.2.1, q.z, hq.2.2.2.2.2.1⟩

-- The `c_0` of a solution is determined by its `z`-coordinate.
example (q : DavisPowerSolution) (hq : q.IsValid) :
    q.c0 = davisPowerB / gaussianPDFReal 0 1 q.z :=
  hq.2.2.2.2.2.2

end MathlibExtTest.Probability.ConvexSubGaussianComparisonDavisPowerSystemExistsUnique
