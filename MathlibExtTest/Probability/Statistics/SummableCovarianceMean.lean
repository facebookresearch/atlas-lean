/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.SummableCovarianceMean

/-!
# Tests for sample-mean consistency under summable autocovariances

The smallest sample size, the zero-length sample, the constant sequence, and dimension one
check the boundaries of the variance bound and the two consistency conclusions.
-/

@[expose] public section

namespace MathlibExtTest.Probability.Statistics.SummableCovarianceMean

open MeasureTheory ProbabilityTheory Filter Finset
open scoped Topology ENNReal
open MathlibExt.Probability.Statistics.SummableCovarianceMean

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-! ### Boundary checks -/

/-- Smallest sample size `L = 1`: `Var(Z 0) ≤ γ 0 + 2 ∑_{h≥1} |γ h|`. -/
example {Z : ℕ → Ω → ℝ} (hZ : ∀ i, MemLp (Z i) 2 P) {γ : ℕ → ℝ}
    (hγ : ∀ i h, cov[Z i, Z (i + h); P] = γ h) (hsum : Summable fun h => |γ h|) :
    Var[Z 0; P] ≤ γ 0 + 2 * ∑' h, |γ (h + 1)| := by
  simpa using variance_mean_le hZ hγ hsum 1

/-- `L = 0`: both sides are `0`. -/
example {Z : ℕ → Ω → ℝ} {γ : ℕ → ℝ} :
    Var[fun ω => ((0 : ℕ) : ℝ)⁻¹ * ∑ i ∈ range 0, Z i ω; P] = 0 ∧
      (γ 0 + 2 * ∑' h, |γ (h + 1)|) / ((0 : ℕ) : ℝ) = 0 := by
  refine ⟨?_, by simp⟩
  have h : (fun ω : Ω => ((0 : ℕ) : ℝ)⁻¹ * ∑ i ∈ range 0, Z i ω) = 0 := by
    funext ω; simp
  rw [h, variance_zero]

/-- Zero-variance boundary: a constant sequence satisfies every hypothesis with `γ = 0`, and the
conclusion holds. -/
example (c : ℝ) :
    TendstoInMeasure P (fun (L : ℕ) (_ : Ω) => (L : ℝ)⁻¹ * ∑ _i ∈ range L, c) atTop
      (fun _ => c) :=
  tendstoInMeasure_mean (Z := fun _ _ => c) (γ := fun _ => 0) (fun _ => memLp_const c)
    (fun _ => by simp) (fun _ _ => by simp) (by simp)

/-- Dimension `1` of the vector theorem is the scalar theorem in coordinate `0`. -/
example {Z : ℕ → Ω → (Fin 1 → ℝ)} (hZ : ∀ i j, MemLp (fun ω => Z i ω j) 2 P) {m : Fin 1 → ℝ}
    (hm : ∀ i j, P[fun ω => Z i ω j] = m j) {γ : Fin 1 → ℕ → ℝ}
    (hγ : ∀ j i h, cov[fun ω => Z i ω j, fun ω => Z (i + h) ω j; P] = γ j h)
    (hsum : ∀ j, Summable fun h => |γ j h|) :
    TendstoInMeasure P (fun (L : ℕ) ω => (L : ℝ)⁻¹ • ∑ i ∈ range L, Z i ω) atTop (fun _ => m) :=
  tendstoInMeasure_mean_pi hZ hm hγ hsum

#print axioms MathlibExt.Probability.Statistics.SummableCovarianceMean.variance_mean_le
#print axioms MathlibExt.Probability.Statistics.SummableCovarianceMean.tendsto_integral_sq_mean_sub
#print axioms MathlibExt.Probability.Statistics.SummableCovarianceMean.tendstoInMeasure_mean
#print axioms MathlibExt.Probability.Statistics.SummableCovarianceMean.tendstoInMeasure_mean_pi

end MathlibExtTest.Probability.Statistics.SummableCovarianceMean
