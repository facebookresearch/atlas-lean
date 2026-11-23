/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Statistics.UStatistic
public import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Tests for U-statistics

Degree `0` (the U-statistic is the constant kernel value), the junk value `0` for degree above
the sample size, the top Hoeffding projection `h_m = h`, unbiasedness for a product kernel, and
Hoeffding's variance formula in degree `1` (`Var U = Var h / n`).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace MathlibExtTest.Probability.Statistics.UStatistic

/-- Degree `0`: the U-statistic is the value of the kernel at the empty tuple. -/
example (h : (Fin 0 → ℝ) → ℝ) (x : Fin 3 → ℝ) : uStatistic h x = h Fin.elim0 := by
  simp [uStatistic, Subsingleton.elim (x ∘ _) Fin.elim0]

/-- Degree above the sample size: there are no injective index maps and the value is the junk
`0`. -/
example (h : (Fin 2 → ℝ) → ℝ) (x : Fin 1 → ℝ) : uStatistic h x = 0 := by
  simp [uStatistic]

/-- The `m`-th Hoeffding projection integrates out nothing: `h_m = h`. -/
example (μ : Measure ℝ) [IsProbabilityMeasure μ] (h : (Fin 2 → ℝ) → ℝ) (y : Fin 2 → ℝ) :
    hoeffdingProj μ h 2 y = h y := by
  change ∫ z : Fin 0 → ℝ, h (fun j => if hj : (j : ℕ) < 2 then y ⟨j, hj⟩ else z ⟨j - 2, _⟩)
    ∂(Measure.pi fun _ => μ) = h y
  rw [integral_unique]
  simp only [probReal_univ, one_smul]
  congr 1
  funext j
  simp [j.isLt]

/-- Unbiasedness for the product kernel `h(y) = y₀ y₁` on a Gaussian sample of size `4`. -/
example :
    ∫ x, uStatistic (fun y : Fin 2 → ℝ => y 0 * y 1) x
        ∂(Measure.pi fun _ : Fin 4 => gaussianReal 0 1) =
      ∫ y, y 0 * y 1 ∂(Measure.pi fun _ : Fin 2 => gaussianReal 0 1) := by
  refine integral_uStatistic (by norm_num) _ ?_
  have h0 := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) 0)
  have h1 := (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
    (measurePreserving_eval (fun _ : Fin 2 => gaussianReal 0 1) 1)
  exact h0.integrable_mul h1

/-- Degree `1`: Hoeffding's formula reduces to `Var U = Var h / n`, here for the identity kernel
on three standard Gaussian observations. -/
example :
    Var[uStatistic (fun y : Fin 1 → ℝ => y 0); Measure.pi fun _ : Fin 3 => gaussianReal 0 1] =
      (Var[hoeffdingProj (gaussianReal 0 1) (fun y : Fin 1 → ℝ => y 0) 1;
        Measure.pi fun _ : Fin 1 => gaussianReal 0 1]) / 3 := by
  have h := variance_uStatistic (m := 1) (n := 3) (by norm_num) (gaussianReal 0 1)
    (h := fun y : Fin 1 → ℝ => y 0) (fun σ y => by rw [Subsingleton.elim σ 1]; rfl)
    ((memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
      (measurePreserving_eval (fun _ : Fin 1 => gaussianReal 0 1) 0))
  rw [h]
  simp

end MathlibExtTest.Probability.Statistics.UStatistic
