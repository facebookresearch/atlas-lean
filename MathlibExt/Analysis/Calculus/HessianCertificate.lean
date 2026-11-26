/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.Analysis.Calculus.LineHessian
public import Mathlib.Analysis.Calculus.Taylor
public import Mathlib.Analysis.InnerProductSpace.EuclideanDist
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Hessian-to-error certificate at the origin

If `g` is `C²` at every point of the closed radius-`R` ball and
its Hessian operator norm is at most `M` there, then the
first-order model at the origin approximates `g` on that ball
with error at most `M * R ^ 2 / 2`. The constant `1 / 2` is
sharp (attained by a quadratic).

## Main results

- `hessian_error_certificate`: the error bound.
-/

@[expose] public section

/-- Origin-centered Hessian-to-error certificate. If `g` is `C²`
at every point of the closed radius-`R` ball and its Hessian
operator norm is at most `M` there, then the first-order model
`z ↦ g 0 + fderiv ℝ g 0 z` approximates `g` on that ball with
error at most `M * R ^ 2 / 2`. The expansion point is the origin;
no recentered tail is used. -/
theorem hessian_error_certificate {n : ℕ}
    {g : EuclideanSpace ℝ (Fin n) → ℝ} {M R : ℝ} (hR : 0 ≤ R)
    (hC2 : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
      ContDiffAt ℝ 2 g y)
    (hH : ∀ y ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R,
      ‖fderiv ℝ (fderiv ℝ g) y‖ ≤ M)
    {z : EuclideanSpace ℝ (Fin n)}
    (hz : z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :
    |g z - (g 0 + fderiv ℝ g 0 z)| ≤ M * R ^ 2 / 2 := by
  have h0mem : (0 : EuclideanSpace ℝ (Fin n)) ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R := by
    rw [Metric.mem_closedBall, dist_self]
    exact hR
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (fderiv ℝ (fderiv ℝ g) 0)) (hH 0 h0mem)
  have hzNorm : ‖z‖ ≤ R := by
    have h := hz
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact h
  have hMaps : Set.MapsTo (fun s : ℝ => (0 : EuclideanSpace ℝ (Fin n)) + s • z)
      (Set.uIcc (0:ℝ) 1) (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) := by
    intro s hs
    have hs01 : s ∈ Set.Icc (0:ℝ) 1 := by
      have : Set.uIcc (0:ℝ) 1 = Set.Icc (0:ℝ) 1 := Set.uIcc_of_le (by norm_num)
      rwa [this] at hs
    obtain ⟨hs0, hs1⟩ := hs01
    rw [Metric.mem_closedBall, dist_zero_right]
    calc ‖(0 : EuclideanSpace ℝ (Fin n)) + s • z‖
        = ‖s • z‖ := by rw [zero_add]
      _ = ‖s‖ * ‖z‖ := norm_smul s z
      _ = |s| * ‖z‖ := by rw [Real.norm_eq_abs]
      _ ≤ 1 * R := by
          apply mul_le_mul _ hzNorm (norm_nonneg _) (by norm_num)
          rw [abs_of_nonneg hs0]
          exact hs1
      _ = R := one_mul R
  have hgOn : ContDiffOn ℝ 2 g (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R) :=
    fun y hy => (hC2 y hy).contDiffWithinAt
  have hinner : ContDiff ℝ 2 (fun s : ℝ => (0 : EuclideanSpace ℝ (Fin n)) + s • z) := by
    fun_prop
  have hφOn : ContDiffOn ℝ 2 (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z))
      (Set.uIcc (0:ℝ) 1) := by
    have hcomp := hgOn.comp hinner.contDiffOn hMaps
    simpa [Function.comp_def] using hcomp
  have hφOn' : ContDiffOn ℝ (1 + 1) (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z))
      (Set.uIcc (0:ℝ) 1) := hφOn
  obtain ⟨x', hx'mem, hx'eq⟩ :=
    taylor_mean_remainder_lagrange_iteratedDeriv (x₀ := 0) (x := 1) (n := 1) (by norm_num) hφOn'
  have h2 : (1 : ℕ) + 1 = 2 := rfl
  rw [h2] at hx'eq
  have hpow : ((1 : ℝ) - 0) ^ (2:ℕ) = 1 := by norm_num
  have hfact : ((Nat.factorial 2 : ℕ) : ℝ) = 2 := by norm_num
  rw [hpow, hfact, mul_one] at hx'eq
  have hTaylor : taylorWithinEval (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) 1
        (Set.uIcc (0:ℝ) 1) 0 1 =
        (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) 0 +
        derivWithin (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z))
          (Set.uIcc (0:ℝ) 1) 0 := by
    have h1 : (1:ℕ) = 0 + 1 := rfl
    rw [h1, taylorWithinEval_succ, taylor_within_zero_eval]
    simp [iteratedDerivWithin_one]
  have hφ0 : (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) 0 = g 0 := by simp
  have hφ1 : (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) 1 = g z := by simp
  have hderiv : derivWithin (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z))
        (Set.uIcc (0:ℝ) 1) 0 = fderiv ℝ g 0 z := by
    have hgDiff : DifferentiableAt ℝ g 0 :=
      (hC2 0 h0mem).differentiableAt (by simp)
    have hinner0 : (0 : EuclideanSpace ℝ (Fin n)) + (0:ℝ) • z = 0 := by simp
    have hgAt : HasFDerivAt g (fderiv ℝ g ((0 : EuclideanSpace ℝ (Fin n)) + (0:ℝ) • z))
        ((0 : EuclideanSpace ℝ (Fin n)) + (0:ℝ) • z) := by
      rw [hinner0]
      exact hgDiff.hasFDerivAt
    have hinnerHas : HasDerivWithinAt (fun s : ℝ => (0 : EuclideanSpace ℝ (Fin n)) + s • z) z
        (Set.uIcc (0:ℝ) 1) 0 := by
      have h1 : HasDerivAt (fun s : ℝ => s • z) ((1 : ℝ) • z) 0 :=
        HasDerivAt.smul_const (hasDerivAt_id' 0) z
      have h2 : HasDerivAt (fun s : ℝ => (0 : EuclideanSpace ℝ (Fin n)) + s • z) ((1 : ℝ) • z) 0 :=
        HasDerivAt.const_add 0 h1
      simpa using h2.hasDerivWithinAt
    have hcomp : HasDerivWithinAt (g ∘ (fun s : ℝ => (0 : EuclideanSpace ℝ (Fin n)) + s • z))
        ((fderiv ℝ g ((0 : EuclideanSpace ℝ (Fin n)) + (0:ℝ) • z)) z)
        (Set.uIcc (0:ℝ) 1) 0 :=
      hgAt.comp_hasDerivWithinAt 0 hinnerHas
    have heq : (g ∘ (fun s : ℝ => (0 : EuclideanSpace ℝ (Fin n)) + s • z))
        = (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) := rfl
    rw [heq, hinner0] at hcomp
    have huniq : UniqueDiffWithinAt ℝ (Set.uIcc (0:ℝ) 1) 0 :=
      (uniqueDiffOn_uIcc (by norm_num : (0:ℝ) ≠ 1)).uniqueDiffWithinAt (by simp)
    exact hcomp.derivWithin huniq
  have heq : (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) 1 -
        taylorWithinEval (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) 1
          (Set.uIcc (0:ℝ) 1) 0 1 =
        g z - (g 0 + fderiv ℝ g 0 z) := by
    rw [hφ1, hTaylor, hφ0, hderiv]
  have hx'Icc : x' ∈ Set.uIcc (0:ℝ) 1 := by
    have h1 : Set.uIoo (0:ℝ) 1 = Set.Ioo 0 1 := Set.uIoo_of_le (by norm_num)
    have h2 : Set.uIcc (0:ℝ) 1 = Set.Icc 0 1 := Set.uIcc_of_le (by norm_num)
    rw [h1] at hx'mem
    rw [h2]
    exact Set.Ioo_subset_Icc_self hx'mem
  have hmem : (0 : EuclideanSpace ℝ (Fin n)) + x' • z ∈ Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) R :=
    hMaps hx'Icc
  have hD2eq : iteratedDeriv 2 (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) x' =
      deriv (deriv (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z))) x' := by
    have : iteratedDeriv 2 (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z))
        = deriv (deriv (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z))) := by
      rw [show (2:ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
    rw [this]
  have hD2bound : ‖iteratedDeriv 2 (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) x'‖
      ≤ M * ‖z‖ ^ 2 := by
    rw [hD2eq]
    have hbound := LineHessian.norm_deriv_deriv_line_le g 0 z (hC2 _ hmem)
    calc ‖deriv (deriv (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z))) x'‖
        ≤ ‖fderiv ℝ (fderiv ℝ g) ((0 : EuclideanSpace ℝ (Fin n)) + x' • z)‖ * ‖z‖ ^ 2 := hbound
      _ ≤ M * ‖z‖ ^ 2 := by
          apply mul_le_mul_of_nonneg_right (hH _ hmem) (by positivity)
  have hsq : ‖z‖ ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hzNorm 2
  have hMle : M * ‖z‖ ^ 2 ≤ M * R ^ 2 := mul_le_mul_of_nonneg_left hsq hM0
  calc |g z - (g 0 + fderiv ℝ g 0 z)|
      = |(fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) 1 -
        taylorWithinEval (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) 1
          (Set.uIcc (0:ℝ) 1) 0 1| := by rw [heq]
    _ = |iteratedDeriv 2 (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) x' / 2| := by
        rw [hx'eq]
    _ = |iteratedDeriv 2 (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) x'| / 2 := by
        rw [abs_div]
        norm_num
    _ = ‖iteratedDeriv 2 (fun s : ℝ => g ((0 : EuclideanSpace ℝ (Fin n)) + s • z)) x'‖ / 2 := by
        rw [← Real.norm_eq_abs]
    _ ≤ (M * ‖z‖ ^ 2) / 2 := by
        apply div_le_div_of_nonneg_right hD2bound (by norm_num)
    _ ≤ M * R ^ 2 / 2 := by
        apply div_le_div_of_nonneg_right hMle (by norm_num)
