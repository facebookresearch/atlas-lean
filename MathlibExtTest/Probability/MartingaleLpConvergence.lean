/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.MartingaleLpConvergence

/-!
# Tests for `L^p` convergence of martingales

Restatements of the public signature in
`MathlibExt.Probability.MartingaleLpConvergence`, the `p = 2` special
case, and the conditional-expectation martingale of an `L^p` function
as a concrete `L^p`-bounded martingale.
-/

@[expose] public section

open MeasureTheory Filter
open scoped Topology ENNReal NNReal

namespace MathlibExtTest.Probability.MartingaleLpConvergence

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ℱ : Filtration ℕ m0} {X : ℕ → Ω → ℝ}

/-- The `L^p` martingale convergence theorem restates with the exact public signature. -/
example (hmart : Martingale X ℱ μ) {p : ℝ≥0∞} {R : ℝ≥0} (hp : 1 < p) (hp_top : p ≠ ⊤)
    (hbdd : ∀ n, eLpNorm (X n) p μ ≤ R) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
      Tendsto (fun n => eLpNorm (X n - ℱ.limitProcess X μ) p μ) atTop (𝓝 0) :=
  hmart.tendsto_eLpNorm_limitProcess_of_eLpNorm_bdd hp hp_top hbdd

/-- The `p = 2` special case: a square-integrable martingale with uniformly
bounded `L²` norms converges a.e. and in `L²`. -/
example (hmart : Martingale X ℱ μ) {R : ℝ≥0}
    (hbdd : ∀ n, eLpNorm (X n) 2 μ ≤ R) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => X n ω) atTop (𝓝 (ℱ.limitProcess X μ ω))) ∧
      Tendsto (fun n => eLpNorm (X n - ℱ.limitProcess X μ) 2 μ) atTop (𝓝 0) :=
  hmart.tendsto_eLpNorm_limitProcess_of_eLpNorm_bdd (by norm_num) (by simp) hbdd

/-- The conditional-expectation martingale of an `L^p` function is an
`L^p`-bounded martingale (by the `L^p` contraction property of
conditional expectation), so it converges a.e. and in `L^p` to its
limit process. -/
example {p : ℝ≥0∞} {R : ℝ≥0} (hp : 1 < p) (hp_top : p ≠ ⊤) {g : Ω → ℝ}
    (hR : eLpNorm g p μ ≤ R) :
    (∀ᵐ ω ∂μ, Tendsto (fun n => (μ[g | ℱ n]) ω) atTop
        (𝓝 (ℱ.limitProcess (fun n => μ[g | ℱ n]) μ ω))) ∧
      Tendsto (fun n => eLpNorm ((μ[g | ℱ n]) - ℱ.limitProcess (fun n => μ[g | ℱ n]) μ) p μ)
        atTop (𝓝 0) :=
  (martingale_condExp g ℱ μ).tendsto_eLpNorm_limitProcess_of_eLpNorm_bdd hp hp_top
    (fun _ => (eLpNorm_condExp_le_eLpNorm _ hp.le).trans hR)

#print axioms Martingale.tendsto_eLpNorm_limitProcess_of_eLpNorm_bdd

end MathlibExtTest.Probability.MartingaleLpConvergence
