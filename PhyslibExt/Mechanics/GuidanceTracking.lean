/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import PhyslibExt.Mechanics.AttitudePorts
import MathlibExt.Analysis.ODE.InvariantRegions
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Guidance tracking: a feasible saturated scalar attitude-rate trajectory

## i. Overview

A body turns about a fixed principal axis and exchanges angular momentum with a reaction wheel,
in the reduced model of `Mechanics.AttitudePorts`: `I` is the axial inertia with the wheel locked,
`ω` the body rate, `h_w` the wheel's momentum relative to the body and `u_w = h_w'` the commanded
momentum rate, so that `I ω' = τ_ext - u_w` and `h_w' = u_w`. Here `τ_ext = 0`, and the rate
feedback with gain `k > 0` saturates at `U_max > 0`: the body torque is
`τ_b(ω) = clip(-k ω) = max (-U_max) (min (-k ω) U_max)` and the wheel takes its reaction,
`u_w = -τ_b`.

From `|ω₀| ≤ U_max / k` the candidate trajectory is `ω(t) = ω₀ exp(-k t / I)` and
`h_w(t) = h₀ + I ω₀ (1 - exp(-k t / I))`, for `t ≥ 0`. Since `0 < exp(-k t / I) ≤ 1` for `t ≥ 0`,
the rate stays in the unclipped interval `|ω| ≤ U_max / k`, where `τ_b(ω) = -k ω`. The rate is
the scalar exponential solution `MetaMathlibExt.scalar_exp_solution` with rate `-k / I`, so it
solves the saturated closed loop `I ω' = τ_b(ω) = -u_w`, and `h_w' = u_w`: the locked body and
the wheel exchange momentum at the opposite rates `-u_w` and `u_w`, and the pair solves the reduced
plant of `AttitudePorts` with `τ_ext = 0`. The command obeys `|u_w| ≤ U_max`, and the finite
reserve `|h₀| + I |ω₀| ≤ h_max` bounds the wheel momentum by `h_max` on every horizon, so the
trajectory is admissible in the sense of `AttitudePorts.WheelAdmissible`. Sign example: for
`ω₀ > 0` the body torque `-k ω` is negative and the wheel momentum rises from `h₀` toward
`h₀ + I ω₀`.

Outside the unsaturated interval, `|ω₀| > U_max / k`, the feedback is clipped at `t = 0` and the
exponential is not a closed-loop solution there; a saturated arc needs another argument. The
reserve is sufficient, not necessary, and the bound `|u_w| ≤ U_max` is on the commanded momentum
rate, not on the motor torque, which differs from it by the wheel inertia times `ω'`.

Model inputs: the reduced scalar fixed-axis wheel model, constant `I`, `k`, `U_max`, and the
saturated rate feedback. Non-goals: no terminal maneuver, optimizer or generic controller theorem,
no tracking of an approximate trajectory, and no empirical adequacy or system safety claim.

## ii. Key results

- `Mechanics.GuidanceTracking.rateTrajectory_unsaturated`: the rate stays in `|ω| ≤ U_max / k`,
  where the body torque is unclipped.
- `Mechanics.GuidanceTracking.trajectory_reducedPlant`: initial values, `ω' = τ_b(ω) / I`,
  `h_w' = u_w` and `I ω' = 0 - u_w` for `t ≥ 0`.
- `Mechanics.GuidanceTracking.abs_wheelCommand_le`, `abs_wheelMomentum_le`: the command and
  momentum bounds.
- `Mechanics.GuidanceTracking.trajectory_wheelAdmissible`: admissibility on every horizon.
- `Mechanics.GuidanceTracking.rateTrajectory_not_closedLoop`: outside the unsaturated interval
  the exponential fails the closed loop at `t = 0`.

A nonzero admissible trajectory and a torque-feasible one that exceeds the momentum limit are in
`PhyslibExtTest.Mechanics.GuidanceTrackingTest`.

## iii. Table of contents

- A. The saturated rate feedback and the exponential trajectory
- B. The unsaturated interval and the reduced plant
- C. Command and momentum bounds
- D. Outside the unsaturated interval

## iv. References

- B. Wie, *Space Vehicle Dynamics and Control*, 2nd edition, AIAA, 2008 (reaction wheels;
  momentum exchange and wheel momentum saturation).
- F. L. Markley and J. L. Crassidis, *Fundamentals of Spacecraft Attitude Determination and
  Control*, Springer, 2014 (attitude control with reaction wheels).
- `MetaMathlibExt.scalar_exp_solution` and `Mechanics.AttitudePorts`: the scalar exponential
  solution and the reduced wheel model reused here.
-/

@[expose] public section

namespace Mechanics.GuidanceTracking

open Set Mechanics.AttitudePorts

/-! ## A. The saturated rate feedback and the exponential trajectory -/

/-- Saturation of `x` to the interval `[-U_max, U_max]`: `clip(x) = max (-U_max) (min x U_max)`. -/
def clip (Umax x : ℝ) : ℝ := max (-Umax) (min x Umax)

/-- The body torque `τ_b(ω) = clip(-k ω)` of the rate feedback with gain `k` and limit `U_max`. In
the reduced wheel model of `AttitudePorts` it is the torque `-u_w` on the body with the wheel
locked. -/
def bodyTorque (k Umax ω : ℝ) : ℝ := clip Umax (-k * ω)

/-- The wheel command `u_w = -τ_b(ω)`: the commanded rate of the wheel momentum, which takes the
reaction of the body torque. -/
def wheelCommand (k Umax ω : ℝ) : ℝ := -bodyTorque k Umax ω

/-- The rate trajectory `ω(t) = ω₀ exp(-k t / I)`. -/
noncomputable def rateTrajectory (I k ω₀ t : ℝ) : ℝ := ω₀ * Real.exp (-k * t / I)

/-- The wheel momentum trajectory `h_w(t) = h₀ + I ω₀ (1 - exp(-k t / I))`. -/
noncomputable def wheelMomentum (I k ω₀ h₀ t : ℝ) : ℝ :=
  h₀ + I * ω₀ * (1 - Real.exp (-k * t / I))

/-! ## B. The unsaturated interval and the reduced plant -/

/-- The rate trajectory in the form of `MetaMathlibExt.scalar_exp_solution`, with rate `-k / I`. -/
private lemma rateTrajectory_eq (I k ω₀ t : ℝ) :
    rateTrajectory I k ω₀ t = ω₀ * Real.exp (-k / I * t) := by
  unfold rateTrajectory
  congr 2
  ring

/-- For `I, k > 0` and `t ≥ 0` the decay factor `exp(-k t / I)` lies in `(0, 1]`. -/
private lemma decay_mem {I k t : ℝ} (hI : 0 < I) (hk : 0 < k) (ht : 0 ≤ t) :
    0 < Real.exp (-k * t / I) ∧ Real.exp (-k * t / I) ≤ 1 :=
  ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr
    (div_nonpos_of_nonpos_of_nonneg (by nlinarith) hI.le)⟩

/-- A value in `[-U_max, U_max]` is not clipped. -/
private lemma clip_of_abs_le {Umax x : ℝ} (hx : |x| ≤ Umax) : clip Umax x = x := by
  rw [abs_le] at hx
  rw [clip, min_eq_left hx.2, max_eq_right hx.1]

/-- **The trajectory stays in the unclipped interval.** For `I, k > 0`, `|ω₀| ≤ U_max / k` and
`t ≥ 0`, the rate obeys `|ω(t)| ≤ U_max / k`, so the feedback `-k ω(t)` lies in
`[-U_max, U_max]` and the body torque is unclipped: `τ_b(ω(t)) = -k ω(t)`. -/
lemma rateTrajectory_unsaturated {I k Umax ω₀ : ℝ} (hI : 0 < I) (hk : 0 < k)
    (hω₀ : |ω₀| ≤ Umax / k) {t : ℝ} (ht : 0 ≤ t) :
    |rateTrajectory I k ω₀ t| ≤ Umax / k ∧
      bodyTorque k Umax (rateTrajectory I k ω₀ t) = -k * rateTrajectory I k ω₀ t := by
  obtain ⟨he0, he1⟩ := decay_mem hI hk ht
  have hle : |rateTrajectory I k ω₀ t| ≤ Umax / k := by
    rw [rateTrajectory, abs_mul, abs_of_pos he0]
    exact (mul_le_of_le_one_right (abs_nonneg ω₀) he1).trans hω₀
  refine ⟨hle, clip_of_abs_le ?_⟩
  rw [abs_mul, abs_neg, abs_of_pos hk]
  rw [le_div_iff₀ hk] at hle
  linarith

/-- **The trajectory solves the reduced wheel plant.** For `I, k > 0` and `|ω₀| ≤ U_max / k`:
`ω(0) = ω₀` and `h_w(0) = h₀`, and at every `t ≥ 0` the rate has the closed-loop derivative
`ω' = τ_b(ω) / I`, the wheel momentum has the derivative `h_w' = u_w`, and `I ω' = τ_ext - u_w`
with `τ_ext = 0`. These are the body and wheel equations of `AttitudePorts`: the locked body's
momentum changes at the rate `-u_w` and the wheel's at the rate `u_w`. -/
lemma trajectory_reducedPlant {I k Umax ω₀ : ℝ} (hI : 0 < I) (hk : 0 < k)
    (hω₀ : |ω₀| ≤ Umax / k) (h₀ : ℝ) :
    rateTrajectory I k ω₀ 0 = ω₀ ∧ wheelMomentum I k ω₀ h₀ 0 = h₀ ∧
      ∀ t, 0 ≤ t →
        HasDerivAt (rateTrajectory I k ω₀) (bodyTorque k Umax (rateTrajectory I k ω₀ t) / I) t ∧
        HasDerivAt (wheelMomentum I k ω₀ h₀) (wheelCommand k Umax (rateTrajectory I k ω₀ t)) t ∧
        I * (bodyTorque k Umax (rateTrajectory I k ω₀ t) / I) =
          0 - wheelCommand k Umax (rateTrajectory I k ω₀ t) := by
  obtain ⟨h0, hd⟩ := MetaMathlibExt.scalar_exp_solution (rateTrajectory_eq I k ω₀)
  have hI0 : I ≠ 0 := hI.ne'
  refine ⟨h0, by simp [wheelMomentum], fun t ht => ?_⟩
  have hb := (rateTrajectory_unsaturated hI hk hω₀ ht).2
  have hω : HasDerivAt (rateTrajectory I k ω₀)
      (bodyTorque k Umax (rateTrajectory I k ω₀ t) / I) t := by
    rw [hb]
    convert hd t using 1
    ring
  refine ⟨hω, ?_, ?_⟩
  · have hfun : wheelMomentum I k ω₀ h₀ =
        fun s => h₀ + I * ω₀ - I * rateTrajectory I k ω₀ s := by
      funext s
      unfold wheelMomentum rateTrajectory
      ring
    rw [hfun]
    exact ((hω.const_mul I).const_sub (h₀ + I * ω₀)).congr_deriv (by
      rw [wheelCommand]
      field_simp)
  · rw [wheelCommand]
    field_simp
    ring

/-! ## C. Command and momentum bounds -/

/-- **Pointwise command bound.** For `I, k > 0`, `|ω₀| ≤ U_max / k` and `t ≥ 0`, the wheel command
along the trajectory obeys `|u_w(ω(t))| ≤ U_max`. -/
lemma abs_wheelCommand_le {I k Umax ω₀ : ℝ} (hI : 0 < I) (hk : 0 < k)
    (hω₀ : |ω₀| ≤ Umax / k) {t : ℝ} (ht : 0 ≤ t) :
    |wheelCommand k Umax (rateTrajectory I k ω₀ t)| ≤ Umax := by
  obtain ⟨hle, hb⟩ := rateTrajectory_unsaturated hI hk hω₀ ht
  rw [wheelCommand, hb, abs_neg, abs_mul, abs_neg, abs_of_pos hk]
  rw [le_div_iff₀ hk] at hle
  linarith

/-- **Finite momentum reserve.** For `I, k > 0` and `|h₀| + I |ω₀| ≤ h_max` (which forces
`h_max ≥ 0`), the wheel momentum obeys `|h_w(t)| ≤ h_max` at every `t ≥ 0`. -/
lemma abs_wheelMomentum_le {I k ω₀ h₀ hmax : ℝ} (hI : 0 < I) (hk : 0 < k)
    (hres : |h₀| + I * |ω₀| ≤ hmax) {t : ℝ} (ht : 0 ≤ t) :
    |wheelMomentum I k ω₀ h₀ t| ≤ hmax := by
  obtain ⟨he0, he1⟩ := decay_mem hI hk ht
  have h1 : 0 ≤ 1 - Real.exp (-k * t / I) := by linarith
  have hIω : 0 ≤ I * |ω₀| := mul_nonneg hI.le (abs_nonneg _)
  calc |wheelMomentum I k ω₀ h₀ t|
      ≤ |h₀| + |I * ω₀ * (1 - Real.exp (-k * t / I))| := by
        rw [wheelMomentum]
        exact abs_add_le _ _
    _ = |h₀| + I * |ω₀| * (1 - Real.exp (-k * t / I)) := by
        rw [abs_mul, abs_mul, abs_of_pos hI, abs_of_nonneg h1]
    _ ≤ |h₀| + I * |ω₀| := by nlinarith
    _ ≤ hmax := hres

/-- **A feasible trajectory for the reduced wheel plant.** For `I, k > 0`, `|ω₀| ≤ U_max / k` and
`|h₀| + I |ω₀| ≤ h_max`, the command `u_w(ω(t))` and the wheel momentum `h_w` are admissible in
the sense of `AttitudePorts.WheelAdmissible` on every horizon `[0, T]` with `T ≥ 0`. The reserve
does not grow with the horizon. -/
lemma trajectory_wheelAdmissible {I k Umax ω₀ h₀ hmax : ℝ} (hI : 0 < I) (hk : 0 < k)
    (hω₀ : |ω₀| ≤ Umax / k) (hres : |h₀| + I * |ω₀| ≤ hmax) {T : ℝ} (hT : 0 ≤ T) :
    WheelAdmissible Umax hmax T (fun t => wheelCommand k Umax (rateTrajectory I k ω₀ t))
      (wheelMomentum I k ω₀ h₀) := by
  exact ⟨hT, fun t ht =>
    ⟨abs_wheelCommand_le hI hk hω₀ ht.1, abs_wheelMomentum_le hI hk hres ht.1⟩⟩

/-! ## D. Outside the unsaturated interval -/

/-- **Outside the unsaturated interval the exponential is not a closed-loop solution.** For
`I, k, U_max > 0` and `|ω₀| > U_max / k` the feedback `-k ω₀` is clipped, and the exponential `ω`
does not have the closed-loop derivative `τ_b(ω(0)) / I` at `t = 0`: this branch needs another
argument. -/
lemma rateTrajectory_not_closedLoop {I k Umax ω₀ : ℝ} (hI : 0 < I) (hk : 0 < k) (hU : 0 < Umax)
    (hω₀ : Umax / k < |ω₀|) :
    ¬ HasDerivAt (rateTrajectory I k ω₀) (bodyTorque k Umax (rateTrajectory I k ω₀ 0) / I) 0 := by
  intro h
  obtain ⟨h0, hd⟩ := MetaMathlibExt.scalar_exp_solution (rateTrajectory_eq I k ω₀)
  have huniq := h.unique (hd 0)
  rw [h0] at huniq
  have hI0 : I ≠ 0 := hI.ne'
  have hb : bodyTorque k Umax ω₀ = -k * ω₀ := by
    field_simp at huniq
    linarith
  have hlo : -Umax ≤ bodyTorque k Umax ω₀ := le_max_left _ _
  have hhi : bodyTorque k Umax ω₀ ≤ Umax := max_le (by linarith) (min_le_right _ _)
  rw [hb] at hlo hhi
  have hk' : k * |ω₀| ≤ Umax := by
    rw [← abs_of_pos hk, ← abs_mul, abs_le]
    constructor <;> linarith
  have hle : |ω₀| ≤ Umax / k := by
    rw [le_div_iff₀ hk]
    linarith
  linarith

end Mechanics.GuidanceTracking
