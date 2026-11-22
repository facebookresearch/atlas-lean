/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Calculus.LineHessian
public import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum

/-!
# Affine constrained potential minimum bound

If a potential has derivative vanishing on a linear subspace at
`x0`, is `C²` along the segment to `x0 + h` for an admissible
displacement `h` in the subspace, and its Hessian quadratic
form in direction `h` is at least `α * ‖h‖ ^ 2` along that
segment, then the potential increase is at least
`α * ‖h‖ ^ 2 / 2`. Only the affine segment is used; no
curved-constraint rule is asserted.

## Main results

- `affine_potential_minimum_bound`: the quantitative minimum
  bound.
-/

@[expose] public section

/-- Affine constrained quantitative potential minimum. Let `Π`
be a real potential on a normed space, `x0` a point whose
derivative vanishes on a linear subspace `S`, and `h ∈ S` an
admissible displacement. If `Π` is `C²` at every point of the
segment from `x0` to `x0 + h` and its Hessian quadratic form in
direction `h` is at least `α * ‖h‖ ^ 2` along that segment, then
`Π (x0 + h) - Π x0 ≥ α * ‖h‖ ^ 2 / 2`. Only the affine segment is
used; no curved-constraint rule is asserted. -/
theorem affine_potential_minimum_bound {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (S : Submodule ℝ E) {«Π» : E → ℝ} {x0 h : E} {α : ℝ}
    (hh : h ∈ S)
    (hstat : ∀ v ∈ S, fderiv ℝ «Π» x0 v = 0)
    (hC2 : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ContDiffAt ℝ 2 «Π» (x0 + t • h))
    (hH : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      α * ‖h‖ ^ 2
        ≤ (fderiv ℝ (fderiv ℝ «Π») (x0 + t • h)) h h) :
    α * ‖h‖ ^ 2 / 2 ≤ «Π» (x0 + h) - «Π» x0 := by
  have hline : ContDiff ℝ 2 (fun s : ℝ => x0 + s • h) := by fun_prop
  have hline_at : ∀ s : ℝ, HasDerivAt (fun s : ℝ => x0 + s • h) h s := fun s => by
    have h1 : HasDerivAt (fun s : ℝ => s • h) ((1 : ℝ) • h) s :=
      HasDerivAt.smul_const (hasDerivAt_id' s) h
    have h2 := HasDerivAt.const_add x0 h1
    simpa using h2
  have hgC2 : ContDiffOn ℝ 2 (fun s : ℝ => «Π» (x0 + s • h)) (Set.uIcc 0 1) := by
    rw [Set.uIcc_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    intro s hs
    exact ((hC2 s hs).comp s hline.contDiffAt).contDiffWithinAt
  have hderiv0 : deriv (fun s : ℝ => «Π» (x0 + s • h)) 0 = 0 := by
    have hdiffPi : DifferentiableAt ℝ «Π» (x0 + (0 : ℝ) • h) :=
      (hC2 0 (Set.left_mem_Icc.mpr zero_le_one)).differentiableAt (by simp)
    have hdiffL : DifferentiableAt ℝ (fun s : ℝ => x0 + s • h) 0 :=
      (hline_at 0).differentiableAt
    have hcomp := fderiv_comp_deriv (0 : ℝ) hdiffPi hdiffL
    rw [(hline_at 0).deriv] at hcomp
    simp only [zero_smul, add_zero] at hcomp
    rw [hstat h hh] at hcomp
    exact hcomp
  have hwithin0 : iteratedDerivWithin 1 (fun s : ℝ => «Π» (x0 + s • h)) (Set.uIcc 0 1) 0
      = 0 := by
    rw [iteratedDerivWithin_one]
    have hdiff0 : DifferentiableAt ℝ (fun s : ℝ => «Π» (x0 + s • h)) 0 :=
      ((hC2 0 (Set.left_mem_Icc.mpr zero_le_one)).comp 0 hline.contDiffAt).differentiableAt
        (by simp)
    have huniq : UniqueDiffWithinAt ℝ (Set.uIcc (0 : ℝ) 1) 0 :=
      (uniqueDiffOn_uIcc zero_ne_one).uniqueDiffWithinAt
        (Set.mem_uIcc_of_le le_rfl zero_le_one)
    rw [hdiff0.derivWithin huniq]
    exact hderiv0
  have hTaylor : taylorWithinEval (fun s : ℝ => «Π» (x0 + s • h)) 1 (Set.uIcc 0 1) 0 1
      = «Π» x0 := by
    have h1 : (1 : ℕ) = 0 + 1 := rfl
    rw [h1, taylorWithinEval_succ, ← h1, taylor_within_zero_eval, hwithin0, smul_zero,
      add_zero]
    simp [zero_smul]
  obtain ⟨ξ, hξ, hT⟩ := taylor_mean_remainder_lagrange_iteratedDeriv (x₀ := (0 : ℝ))
    (x := (1 : ℝ)) (n := 1) (f := fun s : ℝ => «Π» (x0 + s • h)) (by norm_num) hgC2
  rw [Set.uIoo_of_le (zero_le_one : (0 : ℝ) ≤ 1)] at hξ
  have hξIcc : ξ ∈ Set.Icc (0 : ℝ) 1 := Set.Ioo_subset_Icc_self hξ
  have hD : α * ‖h‖ ^ 2 ≤ iteratedDeriv 2 (fun s : ℝ => «Π» (x0 + s • h)) ξ := by
    have h2 : (2 : ℕ) = 1 + 1 := rfl
    rw [h2, iteratedDeriv_succ, iteratedDeriv_one,
      LineHessian.deriv_deriv_line «Π» x0 h (hC2 ξ hξIcc)]
    exact hH ξ hξIcc
  have h2 : (1 : ℕ) + 1 = 2 := rfl
  rw [hTaylor, h2, Nat.factorial_two] at hT
  simp only [sub_zero, one_pow, mul_one, one_smul] at hT
  rw [hT]
  exact div_le_div_of_nonneg_right hD (show (0 : ℝ) ≤ 2 by norm_num)
