/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Domains.Biology.Ecology.SingularStrategyClassificationBranchingPoint
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! # Tests for mutual invasibility near a singular strategy -/

namespace DomainsTest.Biology.Ecology.SingularStrategyClassificationMutualInvasibility

open WantedExt.Biology.Ecology.SingularStrategyClassificationWanted

private noncomputable def q (c x y : ℝ) : ℝ := (y - x) * (-2 * y - c * x)

-- Compute the second derivatives of the resident and mutant slices independently.
private lemma axis_curvatures (c : ℝ) :
    deriv (deriv (fun x => q c x 0)) 0 = 2 * c ∧ deriv (deriv (q c 0)) 0 = -4 := by
  have hx : (fun x => q c x 0) = fun x => c * x ^ 2 := by
    funext x
    simp only [q]
    ring
  have hy : q c 0 = fun y => -2 * y ^ 2 := by
    funext y
    simp only [q]
    ring
  rw [hx, hy]
  simp only [deriv_const_mul_field', deriv_pow_field, Nat.cast_ofNat, Nat.reduceSub, pow_one,
    deriv_const_mul_id]
  constructor <;> ring

-- The sums have opposite signs, although both mutant second derivatives are negative.
example :
    0 < deriv (deriv (fun x => q 3 x 0)) 0 + deriv (deriv (q 3 0)) 0 ∧
      deriv (deriv (fun x => q 1 x 0)) 0 + deriv (deriv (q 1 0)) 0 < 0 := by
  rw [(axis_curvatures 3).1, (axis_curvatures 3).2, (axis_curvatures 1).1, (axis_curvatures 1).2]
  norm_num

-- The positive-curvature example has both invasions at every positive displacement.
example (e : ℝ) (he : 0 < e) : 0 < q 3 (-e) e ∧ 0 < q 3 e (-e) := by
  have h₁ : q 3 (-e) e = 2 * e ^ 2 := by simp only [q]; ring
  have h₂ : q 3 e (-e) = 2 * e ^ 2 := by simp only [q]; ring
  rw [h₁, h₂]
  exact ⟨mul_pos two_pos (pow_pos he _), mul_pos two_pos (pow_pos he _)⟩

-- The negative-curvature example excludes mutual invasion for every distinct pair, in either order.
example (x y : ℝ) (hne : x ≠ y) : ¬ (0 < q 1 x y ∧ 0 < q 1 y x) := by
  have hsum : q 1 x y + q 1 y x = -(x - y) ^ 2 := by simp only [q]; ring
  have hsq := sq_pos_of_ne_zero (sub_ne_zero.mpr hne)
  intro ⟨hxy, hyx⟩
  linarith only [hsum, hsq, hxy, hyx]

-- In particular, exclusion of mutual invasion does not mean that neither strategy can invade.
example (e : ℝ) (he : 0 < e) : 0 < q 1 (-(2 * e)) (-e) ∧ q 1 (-e) (-(2 * e)) < 0 := by
  have h₁ : q 1 (-(2 * e)) (-e) = 4 * e ^ 2 := by simp only [q]; ring
  have h₂ : q 1 (-e) (-(2 * e)) = -5 * e ^ 2 := by simp only [q]; ring
  rw [h₁, h₂]
  constructor <;> nlinarith only [pow_pos he 2]

-- A client can apply the negative branch to arbitrary nearby pairs, not just symmetric pairs.
example {s : ℝ → ℝ → ℝ} {xs : ℝ} (h : IsSingular s xs) (hneg : sxx s xs xs + syy s xs xs < 0) :
    ∃ δ > 0, ∀ x y, |x - xs| < δ → |y - xs| < δ → x ≠ y → ¬ (0 < s x y ∧ 0 < s y x) :=
  (mutual_invasibility (h := h)).2 hneg

end DomainsTest.Biology.Ecology.SingularStrategyClassificationMutualInvasibility
