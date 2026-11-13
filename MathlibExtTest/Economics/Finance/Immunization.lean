/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.Immunization
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Tests for local (Redington) immunization

The quadratic surplus `r²` (assets `r² + 1`, liabilities `1`) has matched
value, vanishing first derivative, and positive second derivative at `r₀ = 0`,
so the abstract surplus lemma applies; the same differentiable asset and
liability values have matched value, matched first derivatives, and a strictly
larger asset second derivative at `r₀ = 0`, so the Redington theorem applies;
the sign-flipped surplus `-r²` has matched value, vanishing first derivative,
and continuity at `r₀ = 0`, yet no positive `δ` makes it nonnegative on
`|r| < δ`, so the positive second-derivative hypothesis cannot be dropped.
-/

@[expose] public section

namespace MathlibExtTest.Economics.Finance.Immunization

open _root_.MathlibExt.Economics.Finance.Immunization

theorem surplus_quad_eq :
    surplus (fun r : ℝ => r ^ 2 + 1) (fun _ => 1) = fun r => r ^ 2 := by
  funext r
  show (r ^ 2 + 1) - (1 : ℝ) = r ^ 2
  ring

theorem hasDerivAt_quad (x : ℝ) :
    HasDerivAt (fun r : ℝ => r ^ 2) (2 * x) x := by
  have h2 := (hasDerivAt_id x).pow 2
  simpa [Pi.pow_def] using h2

theorem test_surplus_val :
    surplus (fun r : ℝ => r ^ 2 + 1) (fun _ => 1) 2 = 4 := by
  norm_num [surplus]

theorem test_deriv_first :
    deriv (surplus (fun r : ℝ => r ^ 2 + 1) (fun _ => 1)) 0 = 0 := by
  rw [surplus_quad_eq, (hasDerivAt_quad 0).deriv]
  norm_num

theorem deriv_quad_eq : deriv (fun r : ℝ => r ^ 2) = fun r => 2 * r := by
  funext x
  exact (hasDerivAt_quad x).deriv

theorem test_deriv_second :
    0 < deriv (deriv (surplus (fun r : ℝ => r ^ 2 + 1) (fun _ => 1))) 0 := by
  rw [surplus_quad_eq, deriv_quad_eq]
  have h2 : HasDerivAt (fun r : ℝ => 2 * r) 2 0 := by
    have hc := HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_id (0 : ℝ))
    simpa using hc
  rw [h2.deriv]
  norm_num

theorem test_instance :
    ∃ δ > 0, ∀ r, |r - 0| < δ →
      0 ≤ surplus (fun r : ℝ => r ^ 2 + 1) (fun _ => 1) r := by
  refine surplus_nonneg_near_of_matched ?_ ?_ ?_ ?_
  · norm_num [surplus]
  · exact test_deriv_first
  · exact test_deriv_second
  · rw [surplus_quad_eq]
    exact (hasDerivAt_quad 0).continuousAt

theorem deriv_quad_add_one_eq : deriv (fun r : ℝ => r ^ 2 + 1) = fun r => 2 * r := by
  funext x
  exact ((hasDerivAt_quad x).add_const 1).deriv

theorem deriv_one_eq : deriv (fun _ : ℝ => (1 : ℝ)) = fun _ => 0 := by
  funext x
  exact deriv_const x 1

/-- The Redington theorem applies to assets `r² + 1` and liabilities `1` at
`r₀ = 0`: both are differentiable, the values and first derivatives match, and
the asset second derivative `2` exceeds the liability second derivative `0`. -/
theorem test_redington_instance :
    ∃ δ > 0, ∀ r, |r - 0| < δ →
      0 ≤ surplus (fun r : ℝ => r ^ 2 + 1) (fun _ => 1) r := by
  refine redington_immunization ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact Filter.Eventually.of_forall fun x => ((hasDerivAt_quad x).add_const 1).differentiableAt
  · exact Filter.Eventually.of_forall fun x => differentiableAt_const 1
  · rw [deriv_quad_add_one_eq]
    exact (hasDerivAt_id (0 : ℝ)).const_mul 2 |>.differentiableAt
  · rw [deriv_one_eq]
    exact differentiableAt_const 0
  · norm_num
  · rw [deriv_quad_add_one_eq, deriv_one_eq]
    norm_num
  · rw [deriv_quad_add_one_eq, deriv_one_eq, deriv_const]
    have h2 : HasDerivAt (fun r : ℝ => 2 * r) 2 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_mul (2 : ℝ)
    rw [h2.deriv]
    norm_num

theorem surplus_neg_eq :
    surplus (fun _ : ℝ => 1) (fun r : ℝ => r ^ 2 + 1) = -(fun r : ℝ => r ^ 2) := by
  funext r
  show (1 : ℝ) - (r ^ 2 + 1) = -(r ^ 2)
  ring

/-- Sign-flipped surplus has matched value at `r₀ = 0`. -/
theorem test_neg_control_value :
    surplus (fun _ : ℝ => 1) (fun r : ℝ => r ^ 2 + 1) 0 = 0 := by
  norm_num [surplus]

/-- Sign-flipped surplus has vanishing first derivative at `r₀ = 0`. -/
theorem test_neg_control_deriv :
    deriv (surplus (fun _ : ℝ => 1) (fun r : ℝ => r ^ 2 + 1)) 0 = 0 := by
  rw [surplus_neg_eq,
    HasDerivAt.deriv (HasDerivAt.neg (hasDerivAt_quad 0))]
  norm_num

/-- Sign-flipped surplus is continuous at `r₀ = 0`. -/
theorem test_neg_control_cont :
    ContinuousAt (surplus (fun _ : ℝ => 1) (fun r : ℝ => r ^ 2 + 1)) 0 := by
  rw [surplus_neg_eq]
  exact HasDerivAt.continuousAt (HasDerivAt.neg (hasDerivAt_quad 0))

/-- Sign-flipped surplus admits no positive `δ` with nonnegative surplus on
`|r| < δ`: at the witness `r = δ / 2` the surplus is `-(δ / 2)² < 0`. -/
theorem test_neg_control_no_good_delta :
    ¬ ∃ δ > 0, ∀ r, |r - 0| < δ →
      0 ≤ surplus (fun _ : ℝ => 1) (fun r : ℝ => r ^ 2 + 1) r := by
  rintro ⟨δ, hδ, h⟩
  have hbound : |δ / 2 - 0| < δ := by
    rw [sub_zero, abs_of_pos (by linarith)]
    linarith
  have h1 := h (δ / 2) hbound
  rw [surplus_neg_eq] at h1
  have h1' : (0 : ℝ) ≤ -(δ / 2) ^ 2 := h1
  have hsq : 0 < (δ / 2) ^ 2 := by
    apply pow_pos
    linarith
  linarith

end MathlibExtTest.Economics.Finance.Immunization
