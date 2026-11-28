/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import MathlibExt.Analysis.Calculus.CubicTimeScaling
import Mathlib.Tactic.NormNum.RealSqrt

/-! # Examples for cubic time scaling -/

open CubicTimeScaling

namespace CubicTimeScalingTest

-- At duration two, the endpoint problem recovers a particular non-monic cubic.
example (a b c d : ℝ) : RestToRest 2 (cubic a b c d) ↔
    a = 0 ∧ b = 0 ∧ c = 3 / 4 ∧ d = -1 / 4 := by
  convert restToRest_cubic_iff (T := 2) (by norm_num) a b c d using 2
  norm_num

-- Both endpoint derivatives are genuine for the smooth solution.
example : HasDerivAt (scaling 2) 0 0 ∧ HasDerivAt (scaling 2) 0 2 := by
  have h := (scaling_facts (T := 2) (by norm_num)).1
  exact ⟨h.2.1, h.2.2.2⟩

-- On the nonnegative half-line the cusp agrees with t − t²/4; on the nonpositive
-- half-line it agrees with −t − t²/4. Its total `deriv` at zero therefore defaults
-- to zero, not its right-hand velocity. The other three endpoint conditions hold.
private noncomputable def cusp (t : ℝ) : ℝ := |t| - t ^ 2 / 4

private theorem cusp_endpoint_conditions :
    (cusp 0 = 0 ∧ deriv cusp 0 = 0 ∧ cusp 2 = 1 ∧ deriv cusp 2 = 0) ∧
    HasDerivAt cusp 0 2 ∧ HasDerivWithinAt cusp 1 (Set.Ici 0) 0 ∧
    ¬ DifferentiableAt ℝ cusp 0 ∧ ¬ RestToRest 2 cusp := by
  have hq (t : ℝ) : HasDerivAt (fun u : ℝ ↦ u ^ 2 / 4) (t / 2) t := by
    apply (((hasDerivAt_id t).fun_pow 2).div_const 4).congr_deriv
    dsimp
    ring
  have hr (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt cusp (1 - t / 2) (Set.Ici 0) t :=
    ((hasDerivAt_id t).sub (hq t)).hasDerivWithinAt.congr_of_mem
      (fun u hu ↦ by simp [cusp, abs_of_nonneg (Set.mem_Ici.mp hu)]) ht
  have hl : HasDerivWithinAt cusp (-1) (Set.Iic 0) 0 := by
    have h := ((hasDerivAt_id (0 : ℝ)).neg.sub (hq 0)).hasDerivWithinAt (s := Set.Iic 0)
    simpa using h.congr_of_mem (f₁ := cusp)
      (fun u hu ↦ by simp [cusp, abs_of_nonpos (Set.mem_Iic.mp hu)]) Set.self_mem_Iic
  have hright : HasDerivWithinAt cusp 1 (Set.Ici 0) 0 := by simpa using hr 0 le_rfl
  have hn : ¬ DifferentiableAt ℝ cusp 0 := by
    intro h
    have h₁ := (uniqueDiffOn_Ici _ _ Set.self_mem_Ici).eq_deriv _ h.hasDerivAt.hasDerivWithinAt hright
    have h₂ := (uniqueDiffOn_Iic _ _ Set.self_mem_Iic).eq_deriv _ h.hasDerivAt.hasDerivWithinAt hl
    linarith
  have h₂ : HasDerivAt cusp 0 2 := by
    convert (hr 2 (by norm_num)).hasDerivAt (Ici_mem_nhds (by norm_num : (0 : ℝ) < 2)) using 1
    norm_num
  exact ⟨⟨by norm_num [cusp], deriv_zero_of_not_differentiableAt hn, by norm_num [cusp], h₂.deriv⟩,
    h₂, hright, hn, fun h ↦ hn h.2.1.differentiableAt⟩

-- The coordinate is decreasing: the velocity is negative and the endpoint
-- accelerations have opposite signs even though their magnitudes agree.
example : coordinate 2 5 1 (1 / 2) = 35 / 8 ∧ deriv (coordinate 2 5 1) 1 = -3 ∧
    deriv (deriv (coordinate 2 5 1)) 0 = -6 ∧ deriv (deriv (coordinate 2 5 1)) 2 = 6 := by
  have p := coordinateProfile (T := 2) (by norm_num) 5 1
  rw [(p.velocity 1).deriv, (p.acceleration 0).deriv, (p.acceleration 2).deriv]
  norm_num [coordinate, scaling, cubic]

private def start : Bool → ℝ | false => 5 | true => -2
private def finish : Bool → ℝ | false => 1 | true => 4
private def speedLimit : Bool → ℝ | false => 2 | true => 9
private def accelLimit (k : ℝ) : Bool → ℝ | false => 6 | true => k

private theorem sup_bool (f : Bool → ℝ) :
    Finset.univ.sup' Finset.univ_nonempty f = max (f false) (f true) := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff ..).2
    rintro (_ | _) _
    · exact le_max_left ..
    · exact le_max_right ..
  · exact max_le (Finset.le_sup' _ (Finset.mem_univ _)) (Finset.le_sup' _ (Finset.mem_univ _))

-- The first coordinate requires duration 3 from speed. The second requires
-- duration 2, 3, or 6 from acceleration as its acceleration limit is tightened.
example : durationBound start finish speedLimit (accelLimit 9) = 3 ∧
    durationBound start finish speedLimit (accelLimit 4) = 3 ∧
    durationBound start finish speedLimit (accelLimit 1) = 6 := by
  norm_num [durationBound, sup_bool, start, finish, speedLimit, accelLimit]

-- At the common threshold both different limiting constraints hold with equality.
example : Feasible 3 start finish speedLimit (accelLimit 4) ∧
    |deriv (coordinate 3 (start false) (finish false)) (3 / 2)| = speedLimit false ∧
    |deriv (deriv (coordinate 3 (start true) (finish true))) 3| = accelLimit 4 true := by
  have profile := cubicTimeScaling (T := 3) (by norm_num) start finish speedLimit (accelLimit 4)
    (by rintro (_ | _) <;> norm_num [speedLimit]) (by rintro (_ | _) <;> norm_num [accelLimit])
  refine ⟨profile.2.2.2.mpr ?_, ?_, ?_⟩
  · norm_num [durationBound, sup_bool, start, finish, speedLimit, accelLimit]
  · rw [(profile.2.2.1 false).speed_midpoint]
    norm_num [start, finish, speedLimit]
  · rw [(profile.2.2.1 true).accel_end]
    norm_num [start, finish, accelLimit]

-- At duration four the first coordinate's peak speed is acceptable, but the
-- second coordinate exceeds the tighter acceleration limit at time zero.
example : |deriv (coordinate 4 (start false) (finish false)) 2| ≤ speedLimit false ∧
    ¬ Feasible 4 start finish speedLimit (accelLimit 1) := by
  constructor
  · rw [((coordinateProfile (T := 4) (by norm_num) _ _).velocity 2).deriv]
    norm_num [start, finish, speedLimit]
  · intro h
    have hbad := (h true 0 (by constructor <;> norm_num)).2
    rw [((coordinateProfile (T := 4) (by norm_num) _ _).accel_start)] at hbad
    norm_num [start, finish, accelLimit] at hbad

-- With no displacement both derivatives vanish, including at the endpoints.
example (x t : ℝ) {T : ℝ} (hT : 0 < T) : deriv (coordinate T x x) t = 0 ∧
    deriv (deriv (coordinate T x x)) t = 0 := by
  have p := coordinateProfile hT x x
  simp [(p.velocity t).deriv, (p.acceleration t).deriv]

-- Zero is the threshold, not a least *positive* duration.
example {ι : Type*} [Fintype ι] [Nonempty ι] (x v a : ι → ℝ)
    (hv : ∀ i, 0 < v i) (ha : ∀ i, 0 < a i) :
    durationBound x x v a = 0 ∧ ∀ T > 0, Feasible T x x v a := by
  have hz : durationBound x x v a = 0 := by simp [durationBound]
  exact ⟨hz, fun _ hT ↦ (feasible_iff hT x x v a hv ha).mpr (hz ▸ hT.le)⟩

end CubicTimeScalingTest
