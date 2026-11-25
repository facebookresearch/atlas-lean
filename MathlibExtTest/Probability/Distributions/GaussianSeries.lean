/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Probability.Distributions.GaussianSeries

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal ENNReal

-- Variances `2⁻ᵏ`: the series converges in `L²` to a `𝓝(0, 2)` variable.
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 ((1 / 2 : ℝ≥0) ^ k)) P) :
    ∃ S : Ω → ℝ,
      Tendsto (fun n => eLpNorm (fun ω => S ω - ∑ k ∈ Finset.range n, X k ω) 2 P) atTop (nhds 0) ∧
      HasLaw S (gaussianReal 0 2) P := by
  have h2 : ∑' k : ℕ, (1 / 2 : ℝ≥0) ^ k = 2 := NNReal.coe_injective (by
    push_cast; exact tsum_geometric_two)
  obtain ⟨S, hS, hlaw⟩ := hindep.exists_tendsto_eLpNorm_sum_hasLaw_gaussianReal hgauss
    (NNReal.summable_coe.mp (by push_cast; exact summable_geometric_two))
  exact ⟨S, hS, h2 ▸ hlaw⟩

-- Finitely many nonzero variances: the limit has the law of the finite sum.
example {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {X : ℕ → Ω → ℝ} {v : ℕ → ℝ≥0} (hindep : iIndepFun X P)
    (hgauss : ∀ k, HasLaw (X k) (gaussianReal 0 (v k)) P) (hv : ∀ k, 3 ≤ k → v k = 0) :
    ∃ S : Ω → ℝ, HasLaw S (gaussianReal 0 (v 0 + v 1 + v 2)) P := by
  obtain ⟨S, -, hlaw⟩ := hindep.exists_tendsto_eLpNorm_sum_hasLaw_gaussianReal hgauss
    (summable_of_ne_finset_zero (s := Finset.range 3) fun k hk => hv k (by simpa using hk))
  refine ⟨S, ?_⟩
  rwa [tsum_eq_sum (s := Finset.range 3) fun k hk => hv k (by simpa using hk),
    Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one] at hlaw

#print axioms iIndepFun.exists_tendsto_eLpNorm_sum_hasLaw_gaussianReal
