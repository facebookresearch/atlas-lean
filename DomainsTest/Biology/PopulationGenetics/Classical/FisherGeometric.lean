/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.PopulationGenetics.Classical.FisherGeometric

/-! Tests for Fisher's geometric model: generic restatements of the criterion,
endpoints, norm invariance, the one-dimensional value, and the limit. -/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped RealInnerProductSpace

namespace MathlibExtTest.Biology.PopulationGenetics.Classical.FisherGeometric

open MathlibExt.Biology.PopulationGenetics.Classical.FisherGeometric

variable {n : ℕ}

example {a u : EuclideanSpace ℝ (Fin n)} {r : ℝ} (hr : 0 < r) (hu : ‖u‖ = 1) :
    ‖a + r • u‖ < ‖a‖ ↔ ⟪a, u⟫ < -r / 2 :=
  norm_add_smul_lt_iff_inner_lt hr hu

example (a : EuclideanSpace ℝ (Fin n)) : beneficialProb a 0 = 0 :=
  beneficialProb_zero_size a

example (r : ℝ) : beneficialProb (0 : EuclideanSpace ℝ (Fin n)) r = 0 :=
  beneficialProb_at_optimum r

example {a a' : EuclideanSpace ℝ (Fin n)} {r : ℝ} (h : ‖a‖ = ‖a'‖) :
    beneficialProb a r = beneficialProb a' r :=
  beneficialProb_eq_of_norm_eq h

example {a : EuclideanSpace ℝ (Fin 1)} {r : ℝ} (ha : 0 < ‖a‖) (hr : 0 < r) :
    beneficialProb a r = if r < 2 * ‖a‖ then 1 / 2 else 0 :=
  beneficialProb_one_dim ha hr

example {z x : ℝ} (hz : 0 < z) (hx : 0 < x)
    (a : ∀ n : ℕ, EuclideanSpace ℝ (Fin (n + 1))) (ha : ∀ n, ‖a n‖ = z) :
    Tendsto (fun n : ℕ => beneficialProb (a n) (2 * z * x / Real.sqrt (n + 1))) atTop
      (𝓝 (1 - cdf (gaussianReal 0 1) x)) :=
  tendsto_beneficialProb hz hx a ha

end MathlibExtTest.Biology.PopulationGenetics.Classical.FisherGeometric
