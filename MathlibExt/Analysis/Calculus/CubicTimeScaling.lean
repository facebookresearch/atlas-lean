/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Data.Fintype.Basic
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith

/-!
# Cubic time scaling of a straight-line path

`CubicTimeScaling.cubicTimeScaling` characterises the rest-to-rest cubic by its four
coefficients, gives the sharp bounds for the derivatives of each real coordinate, and
solves the simultaneous limit inequalities for the duration. The bounds concern this
particular profile, not all paths with the same endpoints.

K. M. Lynch and F. C. Park, *Modern Robotics: Mechanics, Planning, and Control*,
Cambridge University Press, 2017. The December 30, 2019 preprint of the updated first
edition, §9.2.2.1, pp. 331–332, equations (9.9)–(9.13), gives the coefficients, joint
derivatives and extremal times. The finite maximum in `durationBound` is obtained by
solving the resulting inequalities. Derivatives at both endpoints are those of the
polynomial on the whole real line, without extending the motion by rest.
-/

@[expose] public noncomputable section

namespace CubicTimeScaling

open Set

/-- A general polynomial of degree at most three, in increasing order of coefficients. -/
def cubic (a b c d t : ℝ) : ℝ := a + b * t + c * t ^ 2 + d * t ^ 3

/-- The scalar profile starts at zero, ends at one, and has a two-sided derivative of
zero at each endpoint. The function is defined on the whole real line. -/
def RestToRest (T : ℝ) (f : ℝ → ℝ) : Prop :=
  f 0 = 0 ∧ HasDerivAt f 0 0 ∧ f T = 1 ∧ HasDerivAt f 0 T

/-- The rest-to-rest profile `3(t/T)² − 2(t/T)³`. -/
def scaling (T : ℝ) : ℝ → ℝ := cubic 0 0 (3 / T ^ 2) (-2 / T ^ 3)

private theorem hasDerivAt_cubic (a b c d t : ℝ) :
    HasDerivAt (cubic a b c d) (b + 2 * c * t + 3 * d * t ^ 2) t := by
  have h := hasDerivAt_id t
  apply ((((h.const_mul b).const_add a).add ((h.fun_pow 2).const_mul c)).add
    ((h.fun_pow 3).const_mul d)).congr_deriv
  dsimp
  ring

/-- The four endpoint conditions determine all four coefficients, and conversely. -/
theorem restToRest_cubic_iff {T : ℝ} (hT : 0 < T) (a b c d : ℝ) :
    RestToRest T (cubic a b c d) ↔ a = 0 ∧ b = 0 ∧ c = 3 / T ^ 2 ∧ d = -2 / T ^ 3 := by
  have velocity_zero (t : ℝ) : HasDerivAt (cubic a b c d) 0 t ↔
      b + 2 * c * t + 3 * d * t ^ 2 = 0 :=
    ⟨(hasDerivAt_cubic a b c d t).unique, (hasDerivAt_cubic a b c d t).congr_deriv⟩
  simp only [RestToRest, velocity_zero, cubic]
  constructor
  · rintro ⟨ha, hb, hp, hv⟩
    simp only [mul_zero, zero_pow (by decide : 2 ≠ 0), zero_pow (by decide : 3 ≠ 0),
      add_zero] at ha hb
    subst a
    subst b
    refine ⟨rfl, rfl, (eq_div_iff (pow_ne_zero _ hT.ne')).2 ?_,
      (eq_div_iff (pow_ne_zero _ hT.ne')).2 ?_⟩
    · linear_combination 3 * hp - T * hv
    · linear_combination T * hv - 2 * hp
  · rintro ⟨rfl, rfl, rfl, rfl⟩
    refine ⟨by simp, by simp, ?_, ?_⟩ <;> field_simp <;> ring

/-- Factoring the scaling derivative makes its sign on the duration interval explicit. -/
theorem hasDerivAt_scaling {T : ℝ} (hT : 0 < T) (t : ℝ) :
    HasDerivAt (scaling T) (6 * t * (T - t) / T ^ 3) t := by
  apply (hasDerivAt_cubic ..).congr_deriv
  field_simp
  ring

/-- The scalar profile satisfies the endpoint conditions and takes `[0,T]` monotonically
into `[0,1]`. -/
theorem scaling_facts {T : ℝ} (hT : 0 < T) :
    RestToRest T (scaling T) ∧ MonotoneOn (scaling T) (Icc 0 T) ∧
      MapsTo (scaling T) (Icc 0 T) (Icc 0 1) := by
  have he : RestToRest T (scaling T) := (restToRest_cubic_iff hT ..).2 ⟨rfl, rfl, rfl, rfl⟩
  have hd : Differentiable ℝ (scaling T) := fun t ↦ (hasDerivAt_scaling hT t).differentiableAt
  have hm : MonotoneOn (scaling T) (Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) hd.continuous.continuousOn hd.differentiableOn
    intro t ht
    obtain ⟨ht₀, htT⟩ := interior_subset ht
    rw [(hasDerivAt_scaling hT t).deriv]
    exact div_nonneg (mul_nonneg (by positivity) (sub_nonneg.mpr htT)) (by positivity)
  refine ⟨he, hm, fun t ht ↦ ⟨?_, ?_⟩⟩
  · rw [← he.1]
    exact hm (left_mem_Icc.mpr hT.le) ht ht.1
  · rw [← he.2.2.1]
    exact hm ht (right_mem_Icc.mpr hT.le) ht.2

/-- One coordinate of the straight line from `x` to `y`, with the cubic time scaling. -/
def coordinate (T x y t : ℝ) : ℝ := x + scaling T t * (y - x)

/-- The derivative formulas and their sharp absolute bounds for one coordinate. -/
structure CoordinateProfile (T x y : ℝ) : Prop where
  velocity (t : ℝ) : HasDerivAt (coordinate T x y) (6 * t * (T - t) / T ^ 3 * (y - x)) t
  acceleration (t : ℝ) : HasDerivAt (deriv (coordinate T x y))
    (6 * (T - 2 * t) / T ^ 3 * (y - x)) t
  speed_le (t : ℝ) (ht : t ∈ Icc 0 T) : |deriv (coordinate T x y) t| ≤ 3 / (2 * T) * |y - x|
  accel_le (t : ℝ) (ht : t ∈ Icc 0 T) :
    |deriv (deriv (coordinate T x y)) t| ≤ 6 / T ^ 2 * |y - x|
  speed_midpoint : |deriv (coordinate T x y) (T / 2)| = 3 / (2 * T) * |y - x|
  accel_start : |deriv (deriv (coordinate T x y)) 0| = 6 / T ^ 2 * |y - x|
  accel_end : |deriv (deriv (coordinate T x y)) T| = 6 / T ^ 2 * |y - x|

/-- The first derivative is a parabola times the displacement; its derivative is affine.
The speed peaks at the midpoint and the acceleration magnitude at both endpoints. -/
theorem coordinateProfile {T : ℝ} (hT : 0 < T) (x y : ℝ) : CoordinateProfile T x y := by
  have hv (t : ℝ) : HasDerivAt (coordinate T x y) (6 * t * (T - t) / T ^ 3 * (y - x)) t :=
    ((hasDerivAt_scaling hT t).mul_const (y - x)).const_add x
  have ha (t : ℝ) : HasDerivAt (deriv (coordinate T x y))
      (6 * (T - 2 * t) / T ^ 3 * (y - x)) t := by
    rw [show deriv (coordinate T x y) = _ from funext fun u ↦ (hv u).deriv]
    have h := hasDerivAt_id t
    have hnum := (h.const_mul 6).mul (h.const_sub T)
    apply ((hnum.div_const (T ^ 3)).mul_const (y - x)).congr_deriv
    dsimp
    ring
  refine ⟨hv, ha, ?_, ?_, ?_, ?_, ?_⟩
  · rintro t ⟨ht₀, htT⟩
    rw [(hv t).deriv, abs_mul, abs_of_nonneg (div_nonneg
      (mul_nonneg (by positivity) (sub_nonneg.mpr htT)) (by positivity))]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    field_simp
    nlinarith [sq_nonneg (2 * t - T)]
  · rintro t ⟨ht₀, htT⟩
    rw [(ha t).deriv, abs_mul, abs_div, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 6),
      abs_of_pos (pow_pos hT 3)]
    apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
    have h : |T - 2 * t| ≤ T := abs_le.mpr ⟨by linarith, by linarith⟩
    calc 6 * |T - 2 * t| / T ^ 3 ≤ 6 * T / T ^ 3 := by gcongr
         _ = 6 / T ^ 2 := by field_simp
  · rw [(hv _).deriv, abs_mul, show 6 * (T / 2) * (T - T / 2) / T ^ 3 = 3 / (2 * T) by
      field_simp; ring, abs_of_pos (by positivity)]
  · rw [(ha _).deriv, abs_mul, show 6 * (T - 2 * 0) / T ^ 3 = 6 / T ^ 2 by
      field_simp; ring, abs_of_pos (by positivity)]
  · rw [(ha _).deriv, abs_mul, show 6 * (T - 2 * T) / T ^ 3 = -(6 / T ^ 2) by
      field_simp; ring, abs_neg, abs_of_pos (by positivity)]

variable {ι : Type*}

/-- Every coordinate obeys both limits throughout the closed duration interval. -/
def Feasible (T : ℝ) (x y v a : ι → ℝ) : Prop :=
  ∀ i t, t ∈ Icc 0 T → |deriv (coordinate T (x i) (y i)) t| ≤ v i ∧
    |deriv (deriv (coordinate T (x i) (y i))) t| ≤ a i

/-- The largest of the velocity and acceleration duration thresholds over a nonempty
finite family of coordinates. It is zero for a stationary path. -/
def durationBound [Fintype ι] [Nonempty ι] (x y v a : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty fun i ↦
    max (3 * |y i - x i| / (2 * v i)) (Real.sqrt (6 * |y i - x i| / a i))

private theorem peak_iff {T D v a : ℝ} (hT : 0 < T) (hv : 0 < v) (ha : 0 < a) :
    3 / (2 * T) * D ≤ v ∧ 6 / T ^ 2 * D ≤ a ↔
      max (3 * D / (2 * v)) (Real.sqrt (6 * D / a)) ≤ T := by
  rw [max_le_iff, Real.sqrt_le_left hT.le]
  apply and_congr <;> field_simp

/-- A positive duration is feasible for this cubic exactly when it is at least
`durationBound`. In particular equality suffices if the bound is positive. -/
theorem feasible_iff [Fintype ι] [Nonempty ι] {T : ℝ} (hT : 0 < T) (x y v a : ι → ℝ)
    (hv : ∀ i, 0 < v i) (ha : ∀ i, 0 < a i) :
    Feasible T x y v a ↔ durationBound x y v a ≤ T := by
  simp only [durationBound, Finset.sup'_le_iff, Finset.mem_univ, forall_true_left]
  constructor
  · intro h i
    have p := coordinateProfile hT (x i) (y i)
    apply (peak_iff hT (hv i) (ha i)).mp
    rw [← p.speed_midpoint, ← p.accel_start]
    exact ⟨(h i _ ⟨by positivity, by linarith⟩).1, (h i _ (left_mem_Icc.mpr hT.le)).2⟩
  · intro h i t ht
    have p := coordinateProfile hT (x i) (y i)
    obtain ⟨hs, hb⟩ := (peak_iff hT (hv i) (ha i)).mpr (h i)
    exact ⟨(p.speed_le t ht).trans hs, (p.accel_le t ht).trans hb⟩

/-- **Cubic time scaling of a straight line.** For positive duration and a nonempty finite
family of coordinates with positive limits, the endpoint data determine the cubic's
coefficients uniquely. Its scalar profile runs monotonically from zero to one. Each
coordinate has the derivatives and sharp extrema in `CoordinateProfile`, and the joint
limits hold exactly for durations at least `durationBound`. -/
theorem cubicTimeScaling [Fintype ι] [Nonempty ι] {T : ℝ} (hT : 0 < T) (x y v a : ι → ℝ)
    (hv : ∀ i, 0 < v i) (ha : ∀ i, 0 < a i) :
    (∀ a b c d, RestToRest T (cubic a b c d) ↔
      a = 0 ∧ b = 0 ∧ c = 3 / T ^ 2 ∧ d = -2 / T ^ 3) ∧
    (RestToRest T (scaling T) ∧ MonotoneOn (scaling T) (Icc 0 T) ∧
      MapsTo (scaling T) (Icc 0 T) (Icc 0 1)) ∧
    (∀ i, CoordinateProfile T (x i) (y i)) ∧ (Feasible T x y v a ↔ durationBound x y v a ≤ T) :=
  ⟨restToRest_cubic_iff hT, scaling_facts hT, fun i ↦ coordinateProfile hT (x i) (y i),
    feasible_iff hT x y v a hv ha⟩

end CubicTimeScaling
