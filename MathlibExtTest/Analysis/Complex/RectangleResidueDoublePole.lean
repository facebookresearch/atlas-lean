/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Complex.RectangleResidueDoublePole

/-!
# Tests for the residue theorem on a rectangle with double poles
-/

@[expose] public section

open Filter Topology Complex

private noncomputable def unitSq : RectilinearRectangle := RectilinearRectangle.ofBounds (-1) 1 (-1) 1

/-- **`∮ ds / s² = 0`**: a double pole with no residue. -/
example : unitSq.boundaryIntegral (fun s => ((s - 0) ^ 2)⁻¹) = 0 :=
  RectilinearRectangle.boundaryIntegral_inv_sub_sq_eq_zero unitSq (by simp [unitSq]) (by simp [unitSq])
    (by simp [unitSq]) (by simp [unitSq])

/-- **`∮ (1 / s + 1 / s²) ds = 2πi`**: only the residue counts. -/
example : unitSq.boundaryIntegral (fun s => 1 / s + 1 / s ^ 2) = 2 * (Real.pi : ℂ) * I := by
  have h := RectilinearRectangle.boundaryIntegral_eq_two_pi_mul_I_mul_sum_of_double unitSq {0}
    (fun _ => 1) (fun _ => 1) (fun s => 1 / s + 1 / s ^ 2) (fun _ => 0)
    (fun p hp => by
      rw [Finset.mem_singleton] at hp
      subst hp
      simp [unitSq])
    (differentiableOn_const _) (fun s _ _ => by simp)
  simpa using h

/-- The Perron residue at a simple zero `p = 1` of `f = s - 1`: `-x ^ p / p`. -/
example : ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 1 ∧ ∀ᶠ s in 𝓝[≠] (1 : ℂ),
    -(deriv (fun s : ℂ => s - 1) s / (s - 1)) * (((2 : ℝ) : ℂ) ^ s / s) =
      (-((1 : ℤ) : ℂ) * (((2 : ℝ) : ℂ) ^ (1 : ℂ) / 1)) / (s - 1) + φ s :=
  exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_zpow two_pos one_ne_zero (k := 1)
    analyticAt_const one_ne_zero (Eventually.of_forall fun s => by simp)

/-- At a point where `f` does not vanish (`f = exp`), the residue at `0` is `-f'(0) / f(0)`. -/
example : ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
    -(deriv Complex.exp s / Complex.exp s) * (((2 : ℝ) : ℂ) ^ s / s) =
      (-(deriv Complex.exp 0 / Complex.exp 0)) / (s - 0) + φ s :=
  exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_ne_zero two_pos
    (Complex.differentiable_exp.analyticAt 0) (Complex.exp_ne_zero 0)

/-- At a simple zero at `0` (`f = s`), there is a double pole with leading coefficient `-1` and
residue `-log x`. -/
example : ∃ φ : ℂ → ℂ, DifferentiableAt ℂ φ 0 ∧ ∀ᶠ s in 𝓝[≠] (0 : ℂ),
    -(deriv (fun s : ℂ => s) s / s) * (((2 : ℝ) : ℂ) ^ s / s) =
      (-(Real.log 2 : ℂ) - deriv (fun _ : ℂ => (1 : ℂ)) 0 / (1 : ℂ)) / (s - 0) +
        (-1) / (s - 0) ^ 2 + φ s :=
  exists_eventually_neg_logDeriv_mul_cpow_div_eq_of_eq_mul (f := fun s : ℂ => s)
    (E := fun _ : ℂ => (1 : ℂ)) two_pos analyticAt_const one_ne_zero
    (Eventually.of_forall fun s => by simp)
