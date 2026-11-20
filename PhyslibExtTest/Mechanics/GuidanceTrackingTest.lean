/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import PhyslibExt.Mechanics.GuidanceTracking
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

end PhyslibExtTest.Mechanics.GuidanceTracking
