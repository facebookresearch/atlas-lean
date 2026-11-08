/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Analysis.Convex.GradientDescentExponent
public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.Convex.Mul
import Mathlib.Tactic.Module

@[expose] public section

namespace MathlibExtTest.GradientDescentExponent

noncomputable def quadratic
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (x : E) : ℝ :=
  (1 / 2 : ℝ) * ‖x‖ ^ 2

theorem quadratic_hasGradientAt
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) : HasGradientAt quadratic x x := by
  rw [hasGradientAt_iff_hasFDerivAt]
  change HasFDerivAt (fun y : E => (1 / 2 : ℝ) * ‖y‖ ^ 2)
    ((InnerProductSpace.toDual ℝ E) x) x
  convert! (hasStrictFDerivAt_norm_sq x).hasFDerivAt.const_mul (1 / 2 : ℝ) using 1
  ext y
  simp [InnerProductSpace.toDual_apply_apply, innerSL_apply_apply]

theorem quadratic_gradient
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    (x : E) : gradient quadratic x = x := (quadratic_hasGradientAt x).gradient

theorem quadratic_isUnitSmoothConvex
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] :
    IsUnitSmoothConvex (quadratic (E := E)) := by
  refine ⟨?_, fun x => (quadratic_hasGradientAt x).differentiableAt, ?_⟩
  · change ConvexOn ℝ Set.univ (fun x : E => (1 / 2 : ℝ) * ‖x‖ ^ 2)
    have h : ConvexOn ℝ Set.univ (fun x : E => ‖x‖ ^ 2) :=
      (convexOn_norm (E := E) (s := Set.univ) convex_univ).pow
        (fun (x : E) _ => norm_nonneg x) 2
    simpa only [smul_eq_mul] using h.smul (c := (1 / 2 : ℝ)) (by norm_num)
  · rw [show gradient (quadratic (E := E)) = id by ext x; exact quadratic_gradient x]
    exact LipschitzWith.id

noncomputable def initialPoint : EuclideanSpace ℝ (Fin 1) :=
  EuclideanSpace.single 0 1

example : ‖initialPoint‖ = 1 := by
  norm_num [initialPoint, EuclideanSpace.single, PiLp.norm_single]

example : quadratic initialPoint = 1 / 2 := by
  norm_num [quadratic, initialPoint, EuclideanSpace.single, PiLp.norm_single]

example : IsUnitSmoothConvex (quadratic (E := EuclideanSpace ℝ (Fin 1))) :=
  quadratic_isUnitSmoothConvex

example : gradient quadratic initialPoint = initialPoint := quadratic_gradient _

example : gradientDescentTrajectory quadratic (fun _ => 1) initialPoint 1 = 0 := by
  simp [gradientDescentTrajectory_succ, quadratic_gradient]

example : gradientDescentTrajectory quadratic (fun _ => 0) initialPoint 4 = initialPoint := by
  simp

example : gradientDescentTrajectory quadratic (fun _ => -1) initialPoint 1 =
    2 • initialPoint := by
  simp [gradientDescentTrajectory_succ, quadratic_gradient, two_smul]

example : quadratic (gradientDescentTrajectory quadratic (fun _ => 3) initialPoint 1) = 2 := by
  simp only [gradientDescentTrajectory_succ, gradientDescentTrajectory_zero,
    quadratic_gradient]
  rw [show initialPoint - (3 : ℝ) • initialPoint = (-2 : ℝ) • initialPoint by module]
  norm_num [quadratic, norm_smul, initialPoint, EuclideanSpace.single, PiLp.norm_single]

example : gradientDescentTrajectory quadratic (fun k => if k = 0 then 1 / 2 else 3 / 2)
    initialPoint 2 = (-1 / 4 : ℝ) • initialPoint := by
  simp [gradientDescentTrajectory_succ, quadratic_gradient]
  module

example : quadratic (gradientDescentTrajectory quadratic
    (fun k => if k = 0 then 1 / 2 else 3 / 2) initialPoint 2) = 1 / 32 := by
  simp only [gradientDescentTrajectory_succ, gradientDescentTrajectory_zero,
    quadratic_gradient]
  norm_num
  rw [show initialPoint - (1 / 2 : ℝ) • initialPoint -
      (3 / 2 : ℝ) • (initialPoint - (1 / 2 : ℝ) • initialPoint) =
      (-1 / 4 : ℝ) • initialPoint by module]
  norm_num [quadratic, norm_smul, initialPoint, EuclideanSpace.single, PiLp.norm_single]

example : quadratic (gradientDescentTrajectory quadratic (fun _ => 1) initialPoint 1) -
    quadratic (0 : EuclideanSpace ℝ (Fin 1)) ≤
      (1 / 2 : ℝ) * ‖initialPoint - 0‖ ^ 2 / (1 : ℝ) ^ (1 : ℝ) := by
  have h := MetaMathlibExt.gradient_descent_convex_sublinear_rate
    (f := quadratic (E := EuclideanSpace ℝ (Fin 1))) (L := 1) (by norm_num)
    quadratic_isUnitSmoothConvex.1 quadratic_isUnitSmoothConvex.2.1
    quadratic_isUnitSmoothConvex.2.2 (xstar := 0) (by intro x; simp [quadratic])
    (η := 1) (by norm_num) (X := gradientDescentTrajectory quadratic (fun _ => 1) initialPoint)
    (fun k => gradientDescentTrajectory_succ _ _ _ k) 1 (by decide)
  convert h using 1
  simp only [gradientDescentTrajectory_zero, Real.rpow_one]
  ring

example : ∃ C : ℝ, 0 < C ∧ ∃ K : ℕ, 0 < K ∧
    quadratic (gradientDescentTrajectory quadratic (fun _ => 1) initialPoint K) -
        quadratic (0 : EuclideanSpace ℝ (Fin 1)) ≤
          C * ‖initialPoint - 0‖ ^ 2 / (K : ℝ) ^ (1 : ℝ) := by
  rcases gradientDescentUniformRate_one with ⟨C, hC, K, hK, hrate⟩
  refine ⟨C, hC, K, hK, ?_⟩
  exact hrate 1 quadratic quadratic_isUnitSmoothConvex 0
    (by intro x; simp [quadratic]) initialPoint K le_rfl

example : GradientDescentUniformRate (fun _ => 1) 1 := gradientDescentUniformRate_one

example : (1 : EReal) ≤ gradientDescentExponent := one_le_gradientDescentExponent

example : silverGradientDescentSchedule 0 = Real.sqrt 2 := by
  have hs := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  have hne : (1 : ℝ) + Real.sqrt 2 ≠ 0 := by positivity
  norm_num [silverGradientDescentSchedule, gradientDescentSilverRatio, padicValNat_one_right]
  field_simp [hne]
  nlinarith

example : silverGradientDescentSchedule 1 = 2 := by
  have h : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  norm_num [silverGradientDescentSchedule]

example : silverGradientDescentSchedule 2 = silverGradientDescentSchedule 0 := by
  have h : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  simp [silverGradientDescentSchedule, h, padicValNat_one_right]

/-- Bounded actual-quadratic diagnostics adapted from the independent C35
review's SilverPowerPlateauAttempt4, by Codex `/root/finish_c39_current`.
These certify selected horizons, not a general asymptotic refutation theorem. -/
theorem silverQuadraticTrajectory_two :
    gradientDescentTrajectory quadratic silverGradientDescentSchedule initialPoint 2 =
      (gradientDescentSilverRatio⁻¹ : ℝ) • initialPoint := by
  simp only [gradientDescentTrajectory_succ, gradientDescentTrajectory_zero,
    quadratic_gradient, silverGradientDescentSchedule]
  have h2 : padicValNat 2 2 = 1 := padicValNat.self (by decide)
  norm_num [padicValNat_one_right, h2]
  module

theorem silverQuadraticTrajectory_four :
    gradientDescentTrajectory quadratic silverGradientDescentSchedule initialPoint 4 =
      (gradientDescentSilverRatio⁻¹ : ℝ) • initialPoint := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h3 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h4 : padicValNat 2 4 = 2 := by
    simpa only [show (2 : ℕ) ^ 2 = 4 by decide] using
      (padicValNat.prime_pow (p := 2) 2)
  have hrho : gradientDescentSilverRatio ≠ 0 := by
    unfold gradientDescentSilverRatio
    positivity
  rw [show 4 = 3 + 1 by decide, gradientDescentTrajectory_succ]
  rw [show 3 = 2 + 1 by decide, gradientDescentTrajectory_succ, silverQuadraticTrajectory_two]
  simp only [quadratic_gradient, silverGradientDescentSchedule]
  norm_num [h3, h4]
  calc
    _ = (gradientDescentSilverRatio * gradientDescentSilverRatio⁻¹ ^ 2) • initialPoint := by
      module
    _ = gradientDescentSilverRatio⁻¹ • initialPoint := by
      congr 1
      field_simp [hrho]

theorem silverQuadraticTrajectory_eight :
    gradientDescentTrajectory quadratic silverGradientDescentSchedule initialPoint 8 =
      (gradientDescentSilverRatio⁻¹ : ℝ) • initialPoint := by
  let : Fact (Nat.Prime 2) := ⟨by decide⟩
  have h5 : padicValNat 2 5 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h7 : padicValNat 2 7 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
  have h6 : padicValNat 2 6 = 1 := by
    have h3 : padicValNat 2 3 = 0 := padicValNat.eq_zero_of_not_dvd (by norm_num)
    have h2 : padicValNat 2 2 = 1 := padicValNat.self (by decide)
    have h := padicValNat.mul (p := 2) (a := 2) (b := 3) (by decide) (by decide)
    simpa [h3, h2] using h
  have h8 : padicValNat 2 8 = 3 := by
    simpa only [show (2 : ℕ) ^ 3 = 8 by decide] using
      (padicValNat.prime_pow (p := 2) 3)
  have hrho : gradientDescentSilverRatio ≠ 0 := by
    unfold gradientDescentSilverRatio
    positivity
  rw [show 8 = 7 + 1 by decide, gradientDescentTrajectory_succ]
  rw [show 7 = 6 + 1 by decide, gradientDescentTrajectory_succ]
  rw [show 6 = 5 + 1 by decide, gradientDescentTrajectory_succ]
  rw [show 5 = 4 + 1 by decide, gradientDescentTrajectory_succ, silverQuadraticTrajectory_four]
  simp only [quadratic_gradient, silverGradientDescentSchedule]
  norm_num [h5, h6, h7, h8]
  calc
    _ = (gradientDescentSilverRatio ^ 2 * gradientDescentSilverRatio⁻¹ ^ 3) •
        initialPoint := by module
    _ = gradientDescentSilverRatio⁻¹ • initialPoint := by
      congr 1
      field_simp [hrho]

example : quadratic (gradientDescentTrajectory quadratic silverGradientDescentSchedule
    initialPoint 2) = quadratic (gradientDescentTrajectory quadratic silverGradientDescentSchedule
      initialPoint 4) := by
  rw [silverQuadraticTrajectory_two, silverQuadraticTrajectory_four]

example : quadratic (gradientDescentTrajectory quadratic silverGradientDescentSchedule
    initialPoint 4) = quadratic (gradientDescentTrajectory quadratic silverGradientDescentSchedule
      initialPoint 8) := by
  rw [silverQuadraticTrajectory_four, silverQuadraticTrajectory_eight]

example : 0 < quadratic (gradientDescentTrajectory quadratic silverGradientDescentSchedule
    initialPoint 2) := by
  rw [silverQuadraticTrajectory_two]
  have hrho : 0 < gradientDescentSilverRatio := by
    unfold gradientDescentSilverRatio
    positivity
  norm_num [quadratic, norm_smul, initialPoint, EuclideanSpace.single, PiLp.norm_single]
  positivity

end MathlibExtTest.GradientDescentExponent
