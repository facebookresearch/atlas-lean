/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.CanonicalHaarRegularModel
import MathlibExt.Analysis.CStarAlgebra.CrossedProduct.HaarTwistedCore.L1Gauge
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.NormNum

noncomputable section
open MeasureTheory PointNormCStarAction
open scoped CStarAlgebra

namespace CanonicalNormGaugeSmoke

universe uG uA

-- The actual constructed representation has norm two, so it cannot be the identity.
example :
    ‖canonicalCoefficientRepresentation ℂ (2 : ℂ)‖ = 2 ∧
      canonicalCoefficientRepresentation ℂ (2 : ℂ) ≠
        ContinuousLinearMap.id ℂ (CanonicalCoefficientSpace ℂ) := by
  have hn : ‖canonicalCoefficientRepresentation ℂ (2 : ℂ)‖ = 2 := by
    rw [norm_canonicalCoefficientRepresentation]
    norm_num
  refine ⟨hn, ?_⟩
  intro h
  have hb := ContinuousLinearMap.norm_id_le
    (𝕜 := ℂ) (E := CanonicalCoefficientSpace ℂ)
  rw [← h, hn] at hb
  norm_num at hb

example :
    star (canonicalCoefficientRepresentation ℂ Complex.I) =
      -canonicalCoefficientRepresentation ℂ Complex.I ∧
      canonicalCoefficientRepresentation ℂ Complex.I ≠ 0 := by
  constructor
  · rw [← map_star]
    simp only [Complex.star_def, Complex.conj_I, map_neg]
  · intro h
    have hn : ‖canonicalCoefficientRepresentation ℂ Complex.I‖ = 1 := by
      rw [norm_canonicalCoefficientRepresentation]
      simp
    rw [h, norm_zero] at hn
    norm_num at hn

-- No unit or nontriviality requirement is added for the zero-algebra boundary.
example {A : Type uA} [NonUnitalCStarAlgebra A] :
    ‖canonicalCoefficientRepresentation A (0 : A)‖ = 0 := by
  rw [norm_canonicalCoefficientRepresentation, norm_zero]

-- The gauge uses the genuine complex scalar norm, including for nonunital coefficients.
example {G : Type uG} {A : Type uA} [Monoid G] [TopologicalSpace G] [MeasurableSpace G]
    [NonUnitalCStarAlgebra A] (μ : Measure G) (α : PointNormCStarAction G A)
    (f : HaarTwistedCore.Carrier μ α) :
    HaarTwistedCore.l1Gauge μ α ((2 * Complex.I) • f) =
      2 * HaarTwistedCore.l1Gauge μ α f := by
  rw [HaarTwistedCore.l1Gauge_smul]
  norm_num [norm_mul]

end CanonicalNormGaugeSmoke
