/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleSqrtTrick

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleSqrtTrick`

On `ConfigSpace (Fin 2)` with the Dirac measure at the all-open configuration (positively
associated: shown here) and the two increasing events `A i = {ω | ω i = true}`:
* `finite_complUnion_fkg_bound` (FKG product bound for the union complement);
* `finite_symmetric_sqrt_trick` and `finite_symmetric_deficit` (equal probabilities `1`);
* the conditional `PositivelyAssociated` hypothesis is satisfiable.
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleSqrtTrick

open _root_.StatMech _root_.StatMech.BeffaraDC _root_.StatMech.Universality MeasureTheory

/-- The all-open configuration. -/
def top2 : ConfigSpace (Fin 2) := fun _ => true

/-- A Dirac measure is positively associated. -/
theorem dirac_positivelyAssociated : PositivelyAssociated (Measure.dirac top2) := by
  intro A B _ _
  by_cases ha : top2 ∈ A <;> by_cases hb : top2 ∈ B <;>
    simp [Measure.real, Measure.dirac_apply, ha, hb]

/-- The event "edge `i` is open". -/
def openAt (i : Fin 2) : Set (ConfigSpace (Fin 2)) := {ω | ω i = true}

/-- "Edge `i` is open" is increasing. -/
theorem openAt_isIncreasing (i : Fin 2) : IsIncreasing (openAt i) := by
  intro x y hxy hx
  have h := hxy i
  simp only [openAt, Set.mem_ofPred_eq] at hx ⊢
  rw [hx] at h
  exact top_le_iff.mp h

/-- "Edge `i` is open" is measurable. -/
theorem openAt_measurable (i : Fin 2) : MeasurableSet (openAt i) :=
  (Set.toFinite _).measurableSet

/-- Every `openAt i` has Dirac probability `1`. -/
theorem dirac_openAt (i : Fin 2) : (Measure.dirac top2).real (openAt i) = 1 := by
  simp [Measure.real, Measure.dirac_apply_of_mem (show top2 ∈ openAt i from rfl)]

-- The FKG bound on the complement of the union.
example := finite_complUnion_fkg_bound (Measure.dirac top2) dirac_positivelyAssociated
  Finset.univ openAt (fun i _ => openAt_isIncreasing i) (fun i _ => openAt_measurable i)

-- The square-root trick with two symmetric events.
example := finite_symmetric_sqrt_trick (Measure.dirac top2) dirac_positivelyAssociated
  Finset.univ openAt (Finset.mem_univ 0) (fun i _ => openAt_isIncreasing i)
  (fun i _ => openAt_measurable i) (fun i _ => by rw [dirac_openAt, dirac_openAt])

-- The deficit form with `δ = 0`: the union has probability `1`.
example : 1 - (0 : ℝ) ^ ((1 : ℝ) / (Finset.univ : Finset (Fin 2)).card)
    ≤ (Measure.dirac top2).real (openAt 0) :=
  finite_symmetric_deficit (Measure.dirac top2) dirac_positivelyAssociated
    Finset.univ openAt (Finset.mem_univ 0) (fun i _ => openAt_isIncreasing i)
    (fun i _ => openAt_measurable i) (fun i _ => by rw [dirac_openAt, dirac_openAt])
    (by simp [Measure.real, openAt, top2])

end PhyslibExtTest.StatisticalMechanics.RandomCluster.CriticalPoint.LongRectangleSqrtTrick
