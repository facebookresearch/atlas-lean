/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.BrownianMotion.CanonicalBrownianSLE
public import Mathlib

/-!
# Tests for `MathlibExt.Probability.BrownianMotion.CanonicalBrownianSLE`

* `canonicalBrownian_isChordalSLE` at `κ = 2` and `κ = 0`.
* Almost surely the hull at time `1` is a compact hull, `D_1 = ℍ \ K_1`, and `g_1` is a
  homeomorphism `D_1 ≃ ℍ` (for `κ = 4`).
-/

@[expose] public section

open StatMech.SLE MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathlibExtTest.StatMech.Probability.BrownianMotion.CanonicalBrownianSLE

example : IsChordalSLE 2 brownianContinuousModification brownianProductLaw
    (canonicalBrownianLoewnerDomain 2) (canonicalBrownianLoewnerMaps 2) :=
  canonicalBrownian_isChordalSLE 2 (by norm_num)

example : IsChordalSLE 0 brownianContinuousModification brownianProductLaw
    (canonicalBrownianLoewnerDomain 0) (canonicalBrownianLoewnerMaps 0) :=
  canonicalBrownian_isChordalSLE 0 le_rfl

example : ∀ᵐ ω ∂brownianProductLaw, IsCompactHull (canonicalBrownianLoewnerHull 4 ω 1) := by
  filter_upwards [canonicalBrownianLoewnerHull_isCompactHull 4] with ω h
  exact h 1 zero_le_one

example (ω : ℝ → ℝ) : canonicalBrownianLoewnerDomain 4 ω 1 =
    UpperHalfPlane.upperHalfPlaneSet \ canonicalBrownianLoewnerHull 4 ω 1 :=
  canonicalBrownianLoewnerDomain_eq_complement 4 ω 1

example : ∀ᵐ ω ∂brownianProductLaw,
    Nonempty (canonicalBrownianLoewnerDomain 4 ω 1 ≃ₜ UpperHalfPlane.upperHalfPlaneSet) := by
  filter_upwards [canonicalBrownianLoewnerMaps_homeomorph 4] with ω h
  exact h 1 zero_le_one

end MathlibExtTest.StatMech.Probability.BrownianMotion.CanonicalBrownianSLE
