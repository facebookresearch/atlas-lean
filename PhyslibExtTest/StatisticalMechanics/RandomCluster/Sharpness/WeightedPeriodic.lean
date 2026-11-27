/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodic

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodic`

* `phaseSup_critical_eq`: for the two-phase profile `max (β - 3) 0`, the supremum over phases
  has critical point `3`;
* `phaseSup_pos_iff` on an explicit two-phase family;
* `le_phaseEnvelope`: each phase is below the envelope;
* `weighted_periodic_box_differential_inequality`, applied under its nested-domination hypothesis.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodic

open _root_.StatMech _root_.StatMech.OSSS
open Lattice RevealmentConstruction AdaptiveCovLowerGeom
open WiredBoxDifferential FK RevealmentTranslation
open FKSharpnessWeighted FKSharpnessWeightedPeriodic

/-- A two-phase percolation profile with threshold `3`: `θ a β = max (β - 3) 0`. -/
noncomputable def theta3 (_ : Bool) (beta : ℝ) : ℝ := max (beta - 3) 0

/-- `theta3` is positive exactly above `3`. -/
theorem theta3_pos_iff (a : Bool) (beta : ℝ) : 0 < theta3 a beta ↔ 3 < beta := by
  simp [theta3, lt_max_iff, sub_pos]

-- The supremum over phases of `theta3` has critical point `3`.
example : sSup {beta | Finset.univ.sup' Finset.univ_nonempty (fun a => theta3 a beta) = 0} = 3 :=
  phaseSup_critical_eq theta3 3 (fun _ _ => le_max_right _ _) theta3_pos_iff

-- `phaseSup_pos_iff`: the supremum over phases is positive iff some phase is.
example : 0 < Finset.univ.sup' Finset.univ_nonempty (fun a : Bool => if a then (1 : ℝ) else 0) :=
  (phaseSup_pos_iff _).2 ⟨true, by norm_num⟩

-- Each phase is below the envelope.
example (theta : Bool → ℕ → ℝ) (n : ℕ) : theta true n ≤ phaseEnvelope theta n :=
  le_phaseEnvelope theta true n

-- The periodic differential inequality, given nested domination (`d = n = 1`, unit couplings).
example (phase : Site 1 → Unit) (phaseJ : Unit → Sym2 (Site 1) → ℝ)
    (hnested : PeriodicWeightedNestedDomination 1 1 (fun _ => 1) phase phaseJ 2 1) :
    ∃ c : ℝ, 0 < c ∧
      c * (weightedWiredActiveTheta 1 1 (boxCoupling (fun _ => 1) 1) 2 1 /
        weightedPhaseDenom (fun a => weightedPhaseWiredTheta 1 phaseJ a 2 1) 1) ≤
      deriv (fun b => FK.activeBCProbOf (boxGraph 1 1) (wiredBoxBoundaryGraph 1 1)
        (FK.betaParams (boxCoupling (fun _ => 1) 1) b) 2
        (crossEvent (boxActiveEdge 1 1) 0 (vertexBoundary 1 1))) 1 :=
  weighted_periodic_box_differential_inequality 1 1 le_rfl le_rfl (fun _ => 1)
    (fun _ => one_pos) phase phaseJ 2 1 1 (by norm_num) one_pos le_rfl hnested

end PhyslibExtTest.StatisticalMechanics.RandomCluster.Sharpness.WeightedPeriodic
