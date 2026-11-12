/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Economics.Finance.Immunization
import Mathlib.Tactic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow

/-!
# Tests for local (Redington) immunization

The quadratic surplus `r²` (assets `r² + 1`, liabilities `1`) has matched
value, vanishing first derivative, and positive second derivative at `r₀ = 0`,
so the immunization theorem applies; the sign-flipped surplus `-r²` shows the
positive second-derivative hypothesis cannot be dropped.
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

theorem test_neg_control :
    surplus (fun _ : ℝ => 1) (fun r : ℝ => r ^ 2 + 1) 1 = -1 := by
  norm_num [surplus]

end MathlibExtTest.Economics.Finance.Immunization
