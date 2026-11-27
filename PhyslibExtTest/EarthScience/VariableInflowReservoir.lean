/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import PhyslibExt.EarthScience.VariableInflowReservoir
import Mathlib.Analysis.Calculus.Deriv.Add

/-! # Exact finite-interval reservoir profiles -/

open EarthScience Set
open MathlibExt.Biology.Dynamics.FeedForwardLoop (relaxation)

-- At unit recession, inflow `1 + t` gives storage and outflow both equal to `t`.
-- In particular, the integral of net inflow is exactly `T`, not just nonnegative.
example {T : ℝ} (hT : 0 < T) :
    EqOn (relaxation 1 (fun t ↦ 1 + t) 0) id (Icc 0 T) ∧
      (∫ t in (0 : ℝ)..T, (1 + t) - relaxation 1 (fun u ↦ 1 + u) 0 t) = T := by
  have h : IsReservoirStorageOn T 1 (fun t ↦ 1 + t) 0 id := by
    refine ⟨rfl, continuousOn_id, fun t _ ↦ ?_⟩
    simpa using hasDerivAt_id t
  obtain ⟨_, unique, _, budget, _⟩ := linearReservoirWithVariableInflow hT.le 1 0
    (I := fun t ↦ 1 + t) (by fun_prop)
  have hsol := unique id h
  exact ⟨hsol.symm, by simpa [← hsol (right_mem_Icc.mpr hT.le)] using budget.symm⟩

-- The inflow jumps from zero to a negative value at time zero; the competitor is set
-- arbitrarily to 7 outside the interval. Neither extension is assumed continuous there.
example {T : ℝ} (hT : 0 < T) :
    let I := fun t ↦ if t ∈ Icc 0 T then -1 - t else 0
    let Y := fun t ↦ if t ∈ Icc 0 T then -t else 7
    EqOn Y (relaxation 1 I 0) (Icc 0 T) := by
  intro I Y
  have hI : EqOn I (fun t ↦ -1 - t) (Icc 0 T) := fun _ ht ↦ ite_eq_left ht
  have hY : EqOn Y (fun t ↦ -t) (Icc 0 T) := fun _ ht ↦ ite_eq_left ht
  have hc : ContinuousOn I (Icc 0 T) :=
    (by fun_prop : Continuous fun t : ℝ ↦ -1 - t).continuousOn.congr hI
  obtain ⟨_, unique, _⟩ := linearReservoirWithVariableInflow hT.le 1 0 hc
  apply unique
  refine ⟨by simp [Y, hT.le], continuous_id.neg.continuousOn.congr hY, ?_⟩
  intro t ht
  rw [hI (mem_Icc_of_Ioo ht), hY (mem_Icc_of_Ioo ht)]
  have heq := hY.eventuallyEq_of_mem (Icc_mem_nhds ht.1 ht.2)
  simpa using (hasDerivAt_id' t).neg.congr_of_eventuallyEq heq
