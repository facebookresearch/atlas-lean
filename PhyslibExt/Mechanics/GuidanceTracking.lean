/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Analysis.ODE.Gronwall
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
# Guidance tracking: a feasible saturated scalar attitude-rate trajectory and residual tracking

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

Residual tracking. Saturation never increases a difference, so the closed-loop field
`f(ω) = τ_b(ω) / I` satisfies `|f(x) - f(y)| ≤ (k / I) |x - y|` for all rates, whatever `U_max`:
with `I` in kg m² and `k` in N m s/rad it is globally Lipschitz with constant `k / I` (1/s). A
reconstructed rate `φ`, such as an interpolant of a numerical solution, is continuous on `[0, T]`,
has a right derivative `φ'` on `[0, T)`, starts within `δ` of `ω₀`, and satisfies the closed loop
up to a continuous-time residual, `|φ'(t) - f(φ(t))| ≤ ε` on `[0, T)`. For `|ω₀| ≤ U_max / k`,
Grönwall's inequality for approximate solutions against the exponential `ω` bounds the rate error
by `gronwallBound δ (k / I) ε t`. On the horizon `[0, T]` this reads
`|φ(t) - ω(t)| ≤ δ exp(k T / I) + ε (I / k) (exp(k T / I) - 1)`, with `δ` in rad/s, `ε` in rad/s²
and the closed-loop time constant `I / k` in s; a torque residual `ρ = I ε` (N m) turns the second
term into `(ρ / k) (exp(k T / I) - 1)`. The bound grows with the horizon: it is a finite-horizon
estimate, not a uniform one. The error is `φ - ω` and the residual is `φ' - f(φ)`. Sign example:
the straight line `φ(t) = 3/5 - 3 t / 10` starts `1/10` rad/s above `ω₀ = 1/2` (for `I = 2`,
`k = U_max = 1`), and its residual `-3 t / 20` is negative: the line falls faster than the loop
would from the same rate. The field is defined at every rate, so no tube or domain-membership
argument enters, but the residual must be bounded at every time of `[0, T)`: a reconstruction with
zero residual at a list of nodes can still leave the trajectory between them.

Model inputs: the reduced scalar fixed-axis wheel model, constant `I`, `k`, `U_max`, the saturated
rate feedback, and for tracking a reconstruction with its derivative. Non-goals: no terminal
maneuver, optimizer or generic controller theorem; no numerical scheme, error estimator or
step-size rule; tracking concerns the rate only, and no wheel momentum or torque bound is claimed
for a reconstruction; no empirical adequacy or system safety claim.

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
- `Mechanics.GuidanceTracking.lipschitzWith_bodyTorque_div`: the clipped field `τ_b(ω) / I` is
  Lipschitz with constant `k / I`.
- `Mechanics.GuidanceTracking.abs_sub_rateTrajectory_le_gronwallBound`: the rate error of a
  reconstruction is at most `gronwallBound δ (k / I) ε t`.
- `Mechanics.GuidanceTracking.abs_sub_rateTrajectory_le`: the finite-horizon bound in physical
  units.

A nonzero admissible trajectory and a torque-feasible one that exceeds the momentum limit are in
`PhyslibExtTest.Mechanics.GuidanceTrackingTest`, with a reconstruction that has nonzero initial
error and residual, and one whose node residuals vanish but whose rate error does not.

## iii. Table of contents

- A. The saturated rate feedback and the exponential trajectory
- B. The unsaturated interval and the reduced plant
- C. Command and momentum bounds
- D. Outside the unsaturated interval
- E. The Lipschitz field and residual tracking

## iv. References

- B. Wie, *Space Vehicle Dynamics and Control*, 2nd edition, AIAA, 2008 (reaction wheels;
  momentum exchange and wheel momentum saturation).
- F. L. Markley and J. L. Crassidis, *Fundamentals of Spacecraft Attitude Determination and
  Control*, Springer, 2014 (attitude control with reaction wheels).
- J. H. Hubbard and B. H. West, *Differential Equations: A Dynamical Systems Approach*, Part I,
  Springer, 1991, Section 4.5 (the fundamental inequality for approximate solutions).
- H. K. Khalil, *Nonlinear Systems*, 3rd edition, Prentice Hall, 2002, Chapter 3 (Lipschitz
  fields, the Gronwall-Bellman inequality and continuous dependence of solutions).
- `MetaMathlibExt.scalar_exp_solution`, `Mechanics.AttitudePorts`, and Mathlib's `gronwallBound`
  and `dist_le_of_approx_trajectories_ODE_of_mem`: the scalar exponential solution, the reduced
  wheel model and the Grönwall bound reused here.
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

/-! ## E. The Lipschitz field and residual tracking -/

/-- Saturation is `1`-Lipschitz for every limit: `|clip(x) - clip(y)| ≤ |x - y|`. -/
private lemma abs_clip_sub_clip_le (Umax x y : ℝ) : |clip Umax x - clip Umax y| ≤ |x - y| := by
  have h1 := abs_max_sub_max_le_max (-Umax) (min x Umax) (-Umax) (min y Umax)
  have h2 := abs_min_sub_min_le_max x Umax y Umax
  rw [sub_self, abs_zero] at h1 h2
  exact h1.trans (max_le (abs_nonneg _) (h2.trans (max_le le_rfl (abs_nonneg _))))

/-- **The clipped feedback field is globally Lipschitz.** For `I, k > 0` and every limit `U_max`,
the closed-loop field `ω ↦ τ_b(ω) / I = clip(-k ω) / I` satisfies
`|τ_b(x) / I - τ_b(y) / I| ≤ (k / I) |x - y|` for all rates `x, y`: it is Lipschitz on all of `ℝ`
with constant `k / I`, a rate in 1/s. -/
lemma lipschitzWith_bodyTorque_div {I k : ℝ} (hI : 0 < I) (hk : 0 < k) (Umax : ℝ) :
    LipschitzWith (Real.toNNReal (k / I)) fun ω => bodyTorque k Umax ω / I := by
  refine LipschitzWith.of_dist_le_mul fun x y => ?_
  rw [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (div_pos hk hI).le, ← sub_div, abs_div,
    abs_of_pos hI, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hI]
  calc |bodyTorque k Umax x - bodyTorque k Umax y| ≤ |-k * x - -k * y| :=
        abs_clip_sub_clip_le Umax _ _
    _ = k * |x - y| := by
        rw [show -k * x - -k * y = -k * (x - y) by ring, abs_mul, abs_neg, abs_of_pos hk]

/-- **Residual tracking against the feasible trajectory.** Let `I, k > 0` and `|ω₀| ≤ U_max / k`,
so that `ω(t) = ω₀ exp(-k t / I)` solves the closed loop `ω' = τ_b(ω) / I` for `t ≥ 0`. Let the
reconstruction `φ` be continuous on `[0, T]`, with right derivative `φ'` on `[0, T)`, initial
error `|φ(0) - ω₀| ≤ δ` and continuous-time residual `|φ'(t) - τ_b(φ(t)) / I| ≤ ε` on `[0, T)`.
Then `|φ(t) - ω(t)| ≤ gronwallBound δ (k / I) ε t` for every `t ∈ [0, T]`. -/
lemma abs_sub_rateTrajectory_le_gronwallBound {I k Umax ω₀ : ℝ} (hI : 0 < I) (hk : 0 < k)
    (hω₀ : |ω₀| ≤ Umax / k) {φ φ' : ℝ → ℝ} {T δ ε : ℝ} (hφ : ContinuousOn φ (Icc 0 T))
    (hφ' : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (φ' t) (Ici t) t)
    (hres : ∀ t ∈ Ico 0 T, |φ' t - bodyTorque k Umax (φ t) / I| ≤ ε) (h0 : |φ 0 - ω₀| ≤ δ) :
    ∀ t ∈ Icc 0 T, |φ t - rateTrajectory I k ω₀ t| ≤ gronwallBound δ (k / I) ε t := by
  obtain ⟨hω0, -, hd⟩ := trajectory_reducedPlant hI hk hω₀ 0
  intro t ht
  have h := dist_le_of_approx_trajectories_ODE_of_mem (v := fun _ ω => bodyTorque k Umax ω / I)
    (s := fun _ => univ) (K := Real.toNNReal (k / I)) (εf := ε) (εg := 0) (δ := δ)
    (g := rateTrajectory I k ω₀) (g' := fun t => bodyTorque k Umax (rateTrajectory I k ω₀ t) / I)
    (fun _ _ => (lipschitzWith_bodyTorque_div hI hk Umax).lipschitzOnWith) hφ hφ'
    (fun t ht => by rw [Real.dist_eq]; exact hres t ht) (fun _ _ => mem_univ _)
    (fun t ht => (hd t ht.1).1.continuousAt.continuousWithinAt)
    (fun t ht => (hd t ht.1).1.hasDerivWithinAt) (fun t _ => by rw [dist_self])
    (fun _ _ => mem_univ _) (by rw [Real.dist_eq, hω0]; exact h0) t ht
  rwa [Real.dist_eq, Real.coe_toNNReal _ (div_pos hk hI).le, add_zero, sub_zero] at h

/-- **The finite-horizon rate error in physical units.** Let `I, k > 0`, `|ω₀| ≤ U_max / k`, and
let the reconstruction `φ` be continuous on `[0, T]`, with right derivative `φ'` on `[0, T)`,
`|φ(0) - ω₀| ≤ δ` and `|φ'(t) - τ_b(φ(t)) / I| ≤ ε` on `[0, T)`. Then for every `t ∈ [0, T]`
`|φ(t) - ω(t)| ≤ δ exp(k T / I) + ε (I / k) (exp(k T / I) - 1)`. With `ω` and `δ` in rad/s, `ε` in
rad/s², `I` in kg m² and `k` in N m s/rad, the time constant `I / k` is in s and both terms are
rates in rad/s. -/
lemma abs_sub_rateTrajectory_le {I k Umax ω₀ : ℝ} (hI : 0 < I) (hk : 0 < k)
    (hω₀ : |ω₀| ≤ Umax / k) {φ φ' : ℝ → ℝ} {T δ ε : ℝ} (hφ : ContinuousOn φ (Icc 0 T))
    (hφ' : ∀ t ∈ Ico 0 T, HasDerivWithinAt φ (φ' t) (Ici t) t)
    (hres : ∀ t ∈ Ico 0 T, |φ' t - bodyTorque k Umax (φ t) / I| ≤ ε) (h0 : |φ 0 - ω₀| ≤ δ) :
    ∀ t ∈ Icc 0 T, |φ t - rateTrajectory I k ω₀ t| ≤
      δ * Real.exp (k * T / I) + ε * (I / k) * (Real.exp (k * T / I) - 1) := by
  intro t ht
  have hb := abs_sub_rateTrajectory_le_gronwallBound hI hk hω₀ hφ hφ' hres h0 t ht
  have hδ : 0 ≤ δ := (abs_nonneg _).trans h0
  have hmono : gronwallBound δ (k / I) ε t ≤ gronwallBound δ (k / I) ε T := by
    rcases eq_or_lt_of_le ht.2 with h | h
    · rw [h]
    · have hε : 0 ≤ ε := (abs_nonneg _).trans (hres 0 ⟨le_rfl, ht.1.trans_lt h⟩)
      exact gronwallBound_mono hδ hε (div_pos hk hI).le h.le
  refine hb.trans (hmono.trans (le_of_eq ?_))
  rw [gronwallBound_of_K_ne_0 (div_pos hk hI).ne']
  beta_reduce
  rw [show k / I * T = k * T / I by ring, div_div_eq_mul_div ε k I, mul_div_assoc ε I k]

end Mechanics.GuidanceTracking
