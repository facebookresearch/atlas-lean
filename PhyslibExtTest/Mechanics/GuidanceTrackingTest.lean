/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.GuidanceTracking
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Tests for `PhyslibExt.Mechanics.GuidanceTracking`

* The rate `ω₀ = 1/2` with `I = 2`, `k = U_max = 1`, `h₀ = 0` and `h_max = 1`: at `t = 2 log 2`
  the rate is `1/4`, the command `1/4` and the wheel momentum `1/2`, and the trajectory is
  admissible on every horizon. Its closed-loop slope at `t = 0` is `-1/4`, the feedback is
  unclipped at `t = 2 log 2`, the command and momentum bounds hold at every `t ≥ 0`, and the
  merged momentum exchange of `AttitudePorts` keeps `I ω + h_w = 1`.
* The rate `ω₀ = 2` lies above `U_max / k = 1`, and the exponential is not a closed-loop solution
  at `t = 0`.
* With `I = k = U_max = ω₀ = 1`, `h₀ = 0` and `h_max = 1/4` the reserve fails and the wheel
  momentum `1/2` at `t = log 2` exceeds the limit, although the command stays within `1`.
* Residual tracking with `I = 2`, `k = U_max = 1` and `ω₀ = 1/2`: the straight line
  `φ(t) = 3/5 - 3 t / 10` (initial error `1/10`, residual `-3 t / 20`) stays within `4/5` rad/s of
  the trajectory on `[0, 2 log 2]` and within `gronwallBound (1/10) (1/2) (3/10) t` at each time,
  and the clipped field obeys its Lipschitz bound between the saturated rate `2` and rest.
* A reconstruction with zero initial error and zero residual at the nodes `t = 0` and `t = 2`
  still misses the trajectory by `1` rad/s at `t = 1`.
-/

@[expose] public section

namespace PhyslibExtTest.Mechanics.GuidanceTracking

open Set _root_.Mechanics.AttitudePorts _root_.Mechanics.GuidanceTracking

/-- **A nonzero admissible trajectory.** With `I = 2`, `k = 1`, `U_max = 1`, `ω₀ = 1/2`, `h₀ = 0`
and `h_max = 1`: at `t = 2 log 2` the rate is `1/4`, the wheel command `1/4` and the wheel
momentum `1/2`, and the trajectory is admissible on every horizon `[0, T]`, `T ≥ 0`. -/
lemma trajectory_fixture :
    rateTrajectory 2 1 (1 / 2) (2 * Real.log 2) = 1 / 4 ∧
      wheelCommand 1 1 (rateTrajectory 2 1 (1 / 2) (2 * Real.log 2)) = 1 / 4 ∧
      wheelMomentum 2 1 (1 / 2) 0 (2 * Real.log 2) = 1 / 2 ∧
      ∀ T, 0 ≤ T →
        WheelAdmissible 1 1 T (fun t => wheelCommand 1 1 (rateTrajectory 2 1 (1 / 2) t))
          (wheelMomentum 2 1 (1 / 2) 0) := by
  have he : Real.exp (-1 * (2 * Real.log 2) / 2) = 1 / 2 := by
    rw [show -1 * (2 * Real.log 2) / 2 = -Real.log 2 by ring, Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  have hω : rateTrajectory 2 1 (1 / 2) (2 * Real.log 2) = 1 / 4 := by
    rw [rateTrajectory, he]
    norm_num
  refine ⟨hω, ?_, ?_, fun T hT =>
    trajectory_wheelAdmissible (by norm_num) (by norm_num) (by norm_num) (by norm_num) hT⟩
  · rw [hω, wheelCommand, bodyTorque, clip]
    norm_num
  · rw [wheelMomentum, he]
    norm_num

/-- **A torque-feasible trajectory beyond the momentum limit.** With `I = k = U_max = ω₀ = 1`,
`h₀ = 0` and `h_max = 1/4`, the reserve `|h₀| + I |ω₀| ≤ h_max` fails, the wheel momentum reaches
`h_w(log 2) = 1/2 > 1/4`, and the trajectory is not admissible on `[0, log 2]`. -/
lemma reserve_failure_fixture :
    ¬ (|(0 : ℝ)| + 1 * |(1 : ℝ)| ≤ 1 / 4) ∧ wheelMomentum 1 1 1 0 (Real.log 2) = 1 / 2 ∧
      ¬ WheelAdmissible 1 (1 / 4) (Real.log 2)
        (fun t => wheelCommand 1 1 (rateTrajectory 1 1 1 t)) (wheelMomentum 1 1 1 0) := by
  have hh : wheelMomentum 1 1 1 0 (Real.log 2) = 1 / 2 := by
    rw [wheelMomentum, show -1 * Real.log 2 / 1 = -Real.log 2 by ring, Real.exp_neg,
      Real.exp_log (by norm_num)]
    norm_num
  refine ⟨by norm_num, hh, ?_⟩
  rintro ⟨-, hadm⟩
  have hmem : Real.log 2 ∈ Icc 0 (Real.log 2) := ⟨Real.log_nonneg (by norm_num), le_rfl⟩
  have h2 := (hadm _ hmem).2
  rw [hh] at h2
  norm_num at h2

/-- The fixture rate has the closed-loop slope `τ_b(1/2) / 2 = -1/4` at `t = 0`. -/
example : HasDerivAt (rateTrajectory 2 1 (1 / 2)) (-1 / 4) 0 := by
  obtain ⟨h0, -, hd⟩ := trajectory_reducedPlant (I := 2) (k := 1) (Umax := 1) (ω₀ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) 0
  have h := (hd 0 le_rfl).1
  rw [h0] at h
  exact h.congr_deriv (by norm_num [bodyTorque, clip])

/-- At `t = 2 log 2` the fixture rate is inside the unclipped interval, where the body torque is
`-k ω`. -/
example : |rateTrajectory 2 1 (1 / 2) (2 * Real.log 2)| ≤ 1 / 1 ∧
    bodyTorque 1 1 (rateTrajectory 2 1 (1 / 2) (2 * Real.log 2)) =
      -1 * rateTrajectory 2 1 (1 / 2) (2 * Real.log 2) :=
  rateTrajectory_unsaturated (by norm_num) (by norm_num) (by norm_num) (by positivity)

/-- The command and momentum bounds of the fixture at every `t ≥ 0`. -/
example (t : ℝ) (ht : 0 ≤ t) :
    |wheelCommand 1 1 (rateTrajectory 2 1 (1 / 2) t)| ≤ 1 ∧
      |wheelMomentum 2 1 (1 / 2) 0 t| ≤ 1 :=
  ⟨abs_wheelCommand_le (by norm_num) (by norm_num) (by norm_num) ht,
    abs_wheelMomentum_le (by norm_num) (by norm_num) (by norm_num) ht⟩

/-- Momentum exchange along the fixture: the reduced-plant equations feed the merged
`wheel_momentum_exchange`, so `I ω + h_w = I ω₀ + h₀ = 1` on every horizon. -/
example (T : ℝ) :
    ∀ t ∈ Icc 0 T, 2 * rateTrajectory 2 1 (1 / 2) t + wheelMomentum 2 1 (1 / 2) 0 t = 1 := by
  obtain ⟨h0, hh0, hd⟩ := trajectory_reducedPlant (I := 2) (k := 1) (Umax := 1) (ω₀ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) 0
  intro t ht
  have h := (wheel_momentum_exchange (J := 2) (by norm_num) (τ := fun _ => 0)
    (ω' := fun s => bodyTorque 1 1 (rateTrajectory 2 1 (1 / 2) s) / 2)
    (u := fun s => wheelCommand 1 1 (rateTrajectory 2 1 (1 / 2) s))
    (fun s hs => (hd s hs.1).1) (fun s hs => (hd s hs.1).2.1) (fun s hs => (hd s hs.1).2.2)
    (fun _ _ => rfl) t ht).1
  rw [h0, hh0] at h
  linarith

/-- The initial rate `2` lies above `U_max / k = 1`: the exponential is not a closed-loop solution
at `t = 0`. -/
example : ¬ HasDerivAt (rateTrajectory 1 1 2) (bodyTorque 1 1 (rateTrajectory 1 1 2 0) / 1) 0 :=
  rateTrajectory_not_closedLoop (by norm_num) (by norm_num) (by norm_num) (by norm_num)

/-- **A nonzero residual and initial error.** With `I = 2`, `k = U_max = 1` and `ω₀ = 1/2`, the
straight-line reconstruction `φ(t) = 3/5 - 3 t / 10` (one explicit Euler step from a rate read
`1/10` rad/s high) has slope `-3/10` and initial error `|φ(0) - ω₀| = 1/10`, and on `[0, 2 log 2)`
the feedback along it is unclipped and its residual is `φ' - τ_b(φ) / I = -3 t / 20`, of magnitude
below `3/10`. Since `exp(k T / I) = 2` at `T = 2 log 2`, its rate error on `[0, 2 log 2]` is at
most `1/10 · 2 + 3/10 · 2 · (2 - 1) = 4/5` rad/s. -/
lemma tracking_fixture :
    (∀ t, HasDerivAt (fun s : ℝ => 3 / 5 - 3 / 10 * s) (-3 / 10) t) ∧
      (∀ t ∈ Ico 0 (2 * Real.log 2),
        -3 / 10 - bodyTorque 1 1 (3 / 5 - 3 / 10 * t) / 2 = -3 / 20 * t) ∧
      ∀ t ∈ Icc 0 (2 * Real.log 2),
        |3 / 5 - 3 / 10 * t - rateTrajectory 2 1 (1 / 2) t| ≤ 4 / 5 := by
  have hlog : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  have hderiv : ∀ t, HasDerivAt (fun s : ℝ => 3 / 5 - 3 / 10 * s) (-3 / 10) t := fun t =>
    (((hasDerivAt_id t).const_mul (3 / 10 : ℝ)).const_sub (3 / 5 : ℝ)).congr_deriv (by norm_num)
  have hres : ∀ t ∈ Ico 0 (2 * Real.log 2),
      -3 / 10 - bodyTorque 1 1 (3 / 5 - 3 / 10 * t) / 2 = -3 / 20 * t := by
    rintro t ⟨ht0, ht1⟩
    have hc : bodyTorque 1 1 (3 / 5 - 3 / 10 * t) = -1 * (3 / 5 - 3 / 10 * t) := by
      rw [bodyTorque, clip, min_eq_left (by linarith), max_eq_right (by linarith)]
    rw [hc]
    ring
  refine ⟨hderiv, hres, fun t ht => ?_⟩
  have h := abs_sub_rateTrajectory_le (I := 2) (k := 1) (Umax := 1) (ω₀ := 1 / 2)
    (φ := fun s => 3 / 5 - 3 / 10 * s) (φ' := fun _ => -3 / 10) (T := 2 * Real.log 2)
    (δ := 1 / 10) (ε := 3 / 10) (by norm_num) (by norm_num) (by norm_num)
    (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
    (fun s _ => (hderiv s).hasDerivWithinAt)
    (fun s hs => by
      rw [hres s hs, abs_le]
      constructor <;> linarith [hs.1, hs.2])
    (by norm_num) t ht
  have he : Real.exp (1 * (2 * Real.log 2) / 2) = 2 := by
    rw [show 1 * (2 * Real.log 2) / 2 = Real.log 2 by ring, Real.exp_log (by norm_num)]
  rw [he] at h
  linarith

/-- **Node residuals do not certify tracking.** With `I = 2`, `k = U_max = 1` and `ω₀ = 1/2` there
is a differentiable reconstruction `φ` that starts at `ω₀`, meets `ω` again at `t = 2` and has the
closed-loop slope `φ' = τ_b(φ) / I` at both nodes `t = 0` and `t = 2`, so its initial error and
node residuals vanish, yet its rate error on `[0, 2]` is not bounded by
`gronwallBound 0 (k / I) 0 t = 0`, the tracking bound for zero initial and residual bounds. The
witness is `φ(t) = ω(t) + t² (2 - t)²`, whose rate error at `t = 1` is `1` rad/s: changing a
reconstruction between nodes without a new continuous-time residual bound voids the tracking
claim. -/
lemma node_residual_failure_fixture :
    ∃ φ : ℝ → ℝ, Differentiable ℝ φ ∧ φ 0 = 1 / 2 ∧ φ 2 = rateTrajectory 2 1 (1 / 2) 2 ∧
      (∀ s ∈ ({0, 2} : Set ℝ), HasDerivAt φ (bodyTorque 1 1 (φ s) / 2) s) ∧
      ¬ ∀ t ∈ Icc (0 : ℝ) 2,
        |φ t - rateTrajectory 2 1 (1 / 2) t| ≤ gronwallBound 0 (1 / 2) 0 t := by
  obtain ⟨h0, -, hd⟩ := trajectory_reducedPlant (I := 2) (k := 1) (Umax := 1) (ω₀ := 1 / 2)
    (by norm_num) (by norm_num) (by norm_num) 0
  have hb : ∀ s, HasDerivAt (fun t : ℝ => t ^ 2 * (2 - t) ^ 2)
      (2 * s * (2 - s) ^ 2 - 2 * s ^ 2 * (2 - s)) s := fun s => by
    have h := (hasDerivAt_pow 2 s).mul (((hasDerivAt_id s).const_sub 2).pow 2)
    exact h.congr_deriv (by simp; ring)
  refine ⟨fun t => rateTrajectory 2 1 (1 / 2) t + t ^ 2 * (2 - t) ^ 2, ?_, ?_, by simp, ?_, ?_⟩
  · have : Differentiable ℝ (rateTrajectory 2 1 (1 / 2)) := by
      unfold rateTrajectory
      fun_prop
    exact this.add (fun s => (hb s).differentiableAt)
  · simp only [h0]
    norm_num
  · rintro s (rfl | rfl)
    · exact ((hd 0 le_rfl).1.add (hb 0)).congr_deriv (by simp)
    · exact ((hd 2 (by norm_num)).1.add (hb 2)).congr_deriv (by norm_num)
  · intro h
    have h1 := h 1 ⟨by norm_num, by norm_num⟩
    rw [gronwallBound_ε0_δ0] at h1
    norm_num at h1

/-- The clipped field at the saturated rate `2` and at rest obeys the Lipschitz bound
`(k / I) |2 - 0| = 1`. -/
example : |bodyTorque 1 1 2 / 2 - bodyTorque 1 1 0 / 2| ≤ 1 / 2 * |2 - 0| := by
  have hL := lipschitzWith_bodyTorque_div (I := 2) (k := 1) (by norm_num) (by norm_num) 1
  have h := hL.dist_le_mul 2 0
  rwa [Real.dist_eq, Real.dist_eq, Real.coe_toNNReal _ (by norm_num)] at h

/-- The straight-line reconstruction of `tracking_fixture` at each time `t ∈ [0, 2 log 2]`: the
rate error is within `gronwallBound (1/10) (1/2) (3/10) t`. -/
example : ∀ t ∈ Icc 0 (2 * Real.log 2),
    |3 / 5 - 3 / 10 * t - rateTrajectory 2 1 (1 / 2) t| ≤
      gronwallBound (1 / 10) (1 / 2) (3 / 10) t := by
  obtain ⟨hderiv, hres, -⟩ := tracking_fixture
  have hlog : Real.log 2 < 1 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    linarith [Real.add_one_lt_exp (one_ne_zero (α := ℝ))]
  exact abs_sub_rateTrajectory_le_gronwallBound (I := 2) (k := 1) (Umax := 1) (ω₀ := 1 / 2)
    (φ := fun s => 3 / 5 - 3 / 10 * s) (φ' := fun _ => -3 / 10) (by norm_num) (by norm_num)
    (by norm_num) (fun s _ => (hderiv s).continuousAt.continuousWithinAt)
    (fun s _ => (hderiv s).hasDerivWithinAt)
    (fun s hs => by
      rw [hres s hs, abs_le]
      constructor <;> linarith [hs.1, hs.2])
    (by norm_num)

end PhyslibExtTest.Mechanics.GuidanceTracking
