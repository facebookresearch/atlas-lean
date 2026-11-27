/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.SpecialFunctions.GaussianGrowth
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FunProp

open scoped ContDiff
open Set MathlibExt.Analysis.GaussianMoments

open MeasureTheory Real MathlibExt.Analysis

example {a : ℝ} (ha : 0 < a) (c : ℝ) (n : ℕ) :
    Integrable (fun y : ℝ => |y| ^ n * exp (-a * y ^ 2 + c * |y|)) :=
  integrable_pow_mul_exp_neg_sq_add_abs ha c n

-- Arbitrarily large linear growth is absorbed at every positive decay rate.
example : Integrable (fun y : ℝ => |y| ^ 7 * exp (-(1 / 100 : ℝ) * y ^ 2 + 50 * |y|)) :=
  integrable_pow_mul_exp_neg_sq_add_abs (by norm_num) 50 7

example : Integrable (fun y : ℝ => |y| ^ 3 * exp (-2 * y ^ 2 - 4 * |y|)) := by
  simpa only [sub_eq_add_neg, neg_mul] using
    integrable_pow_mul_exp_neg_sq_add_abs (by norm_num : (0 : ℝ) < 2) (-4) 3

example (a : ℝ) : HasExpGrowth (fun x : ℝ => exp (a * x)) := HasExpGrowth.exp_linear a

example : HasExpGrowth (fun x : ℝ => -3 * exp (2 * x)) :=
  (HasExpGrowth.exp_linear 2).const_mul (-3)

example {f : ℝ → ℝ} (hf : HasExpGrowth f) {a : ℝ} (ha : 0 < a) :
    ∃ M, ∀ x, |exp (-a * x ^ 2) * f x| ≤ M := hf.gaussian_damped_bounded ha

example : Integrable (fun y : ℝ => y ^ 4 * exp (-2 * y ^ 2 + 3 * y) * exp (5 * y)) :=
  integrable_gaussianMoment_of_exp_growth (by fun_prop) (HasExpGrowth.exp_linear 5) 4
    (p := (2, 3)) (by norm_num)

-- Both parameter directions, including the sign and order jump in Gaussian decay.
example : HasFDerivAt (gaussianMoment (fun x => exp (3 * x)) 2)
    ((-gaussianMoment (fun x => exp (3 * x)) 4 (1, 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ +
      gaussianMoment (fun x => exp (3 * x)) 3 (1, 2) • ContinuousLinearMap.snd ℝ ℝ ℝ) (1, 2) :=
  gaussianMoment_hasFDerivAt_of_exp_growth (by fun_prop) (HasExpGrowth.exp_linear 3) 2
    (p := (1, 2)) (by norm_num)

example : ContDiffOn ℝ 8 (gaussianMoment (fun x => exp (3 * x)) 5) (Ioi 0 ×ˢ univ) :=
  (gaussianMoment_contDiffOn_of_exp_growth (by fun_prop) (HasExpGrowth.exp_linear 3) 5).of_le (by simp)

-- Positive quadratic decay is essential: the zero and wrong-sign cases fail.
example : ¬ Integrable (fun y : ℝ => exp (0 * y ^ 2)) := by
  simpa using (integrable_exp_neg_mul_sq_iff (b := 0))

example : ¬ Integrable (fun y : ℝ => exp (y ^ 2)) := by
  have h := integrable_exp_neg_mul_sq_iff (b := (-1 : ℝ))
  norm_num at h
  exact h

#print axioms MathlibExt.Analysis.GaussianMoments.gaussianMoment_hasFDerivAt_of_exp_growth
