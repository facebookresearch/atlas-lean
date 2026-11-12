/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.Normed.Group.Basic

@[expose] public section

/-! # KKT sufficiency

For a convex differentiable problem (convexity in first-order
gradient form), a feasible point with nonnegative multipliers
satisfying complementary slackness and stationarity of the
Lagrangian is a global minimizer. This is the sufficiency core of
roadmap package ML-22 of the Atlas TCS canon roadmap; Slater's
condition and necessity are follow-ups.

Source: Boyd and Vandenberghe, Convex Optimization (2004),
Section 5.5.3.
-/

open Finset

/-- KKT sufficiency: let `f` and the constraint functions `g i` be
convex and differentiable on a real inner product space, let `x`
be feasible (`g i x ≤ 0`), and let `lam i ≥ 0` be multipliers with
complementary slackness (`lam i * g i x = 0`) and stationarity
(the gradient of the Lagrangian vanishes at `x`). Then `x`
minimizes `f` over the feasible set. Convexity is stated through
the first-order lower bound with the gradient map `grad`. -/
theorem kkt_sufficient {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {ι : Type*} [Fintype ι]
    {f : E → ℝ} {g : ι → E → ℝ} {gradf : E → E} {gradg : ι → E → E}
    (hf : ∀ x y, f x + @inner ℝ E _ (gradf x) (y - x) ≤ f y)
    (hg : ∀ i x y, g i x + @inner ℝ E _ (gradg i x) (y - x) ≤ g i y)
    (x : E) (lam : ι → ℝ) (hlam : ∀ i, 0 ≤ lam i)
    (hfeas : ∀ i, g i x ≤ 0)
    (hcomp : ∀ i, lam i * g i x = 0)
    (hstat : gradf x + ∑ i, lam i • gradg i x = 0)
    (y : E) (hy : ∀ i, g i y ≤ 0) :
    f x ≤ f y := by
  have _hfeas := hfeas
  have hgi : ∀ i, lam i * @inner ℝ E _ (gradg i x) (y - x) ≤ lam i * g i y := by
    intro i
    have h2 : @inner ℝ E _ (gradg i x) (y - x) ≤ g i y - g i x := by
      have h1 := hg i x y
      linarith
    have h3 := mul_le_mul_of_nonneg_left h2 (hlam i)
    rw [mul_sub, hcomp i, sub_zero] at h3
    exact h3
  have hsum1 : ∑ i, lam i * @inner ℝ E _ (gradg i x) (y - x) ≤ ∑ i, lam i * g i y :=
    Finset.sum_le_sum (fun i _ => hgi i)
  have hsum2 : ∑ i, lam i * g i y ≤ 0 :=
    Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (hlam i) (hy i))
  have hinner : @inner ℝ E _ (∑ i, lam i • gradg i x) (y - x)
      = ∑ i, lam i * @inner ℝ E _ (gradg i x) (y - x) := by
    simp_rw [sum_inner, real_inner_smul_left]
  have hS : @inner ℝ E _ (∑ i, lam i • gradg i x) (y - x) ≤ 0 := by
    rw [hinner]
    exact le_trans hsum1 hsum2
  have hgrad : gradf x = -(∑ i, lam i • gradg i x) := eq_neg_of_add_eq_zero_left hstat
  have hnonneg : 0 ≤ @inner ℝ E _ (gradf x) (y - x) := by
    rw [hgrad, inner_neg_left]
    linarith
  have hfx := hf x y
  linarith
