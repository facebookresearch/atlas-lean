/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import PhyslibExt.StatisticalMechanics.RandomCluster.PeriodicPlanar.Sheffield.Basic

/-!
# FKG does not imply comparisons between increasing events

An FKG measure need not satisfy `μ A ≤ μ B` for arbitrary increasing events `A` and `B`.

## i. Overview

A Dirac mass on a configuration is FKG: every pair of events has correlation zero or one. Take the
all-closed configuration on the single edge of the two-vertex graph. The certain event has mass one
and the increasing event "the edge is open" has mass zero, so the comparison
`μ.real A ≤ μ.real B` fails for this pair of increasing events. The headline
`not_fkg_implies_increasing_event_orientation_comparison` is proved unconditionally. It shows that
any result assuming such a comparison for every FKG measure has an unsatisfiable hypothesis.

## ii. Key results

- `isFKG_dirac` : every Dirac mass on configurations is FKG.
- `not_fkg_implies_increasing_event_orientation_comparison` : FKG measures do not satisfy every
  increasing-event comparison `μ.real A ≤ μ.real B`.

## iii. Table of contents

- A. Dirac masses are FKG
- B. The two-vertex counterexample

## iv. References

- G. Grimmett, *The Random-Cluster Model*, Springer (2006).
-/

@[expose] public section

open MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar

/-! ## A. Dirac masses are FKG -/

/-- A Dirac mass on a configuration is FKG: correlations of events under it are `0` or `1`. -/
theorem isFKG_dirac {V : Type} (omega : ConfigSpace (Sym2 V)) :
    IsFKG (Measure.dirac omega) := by
  intro A B hA hB _hAi _hBi
  rw [Measure.real, Measure.real, Measure.real,
    Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hB,
    Measure.dirac_apply' _ (hA.inter hB)]
  by_cases homegaA : omega ∈ A <;>
    by_cases homegaB : omega ∈ B <;>
      simp [homegaA, homegaB]

/-! ## B. The two-vertex counterexample -/

/-- The all-closed configuration on the edges of the two-vertex graph. -/
def aspectOrientationCounterexampleConfig : ConfigSpace (Sym2 (Fin 2)) :=
  fun _ => false

/-- The certain event on configurations of the two-vertex graph. -/
def aspectOrientationCertainEvent : Set (ConfigSpace (Sym2 (Fin 2))) :=
  Set.univ

/-- The increasing event that the edge `s(0, 1)` is open; it has mass zero under the
counterexample. -/
def aspectOrientationAbsentEvent : Set (ConfigSpace (Sym2 (Fin 2))) :=
  {omega | omega s(0, 1) = true}

lemma aspectOrientationCertainEvent_measurable :
    MeasurableSet aspectOrientationCertainEvent :=
  MeasurableSet.univ

lemma aspectOrientationAbsentEvent_measurable :
    MeasurableSet aspectOrientationAbsentEvent := by
  have hpre : aspectOrientationAbsentEvent =
      (fun omega : ConfigSpace (Sym2 (Fin 2)) => omega s(0, 1)) ⁻¹' {true} := by
    ext omega
    simp [aspectOrientationAbsentEvent]
  rw [hpre]
  exact (measurable_pi_apply s(0, 1)) (measurableSet_singleton true)

lemma aspectOrientationCertainEvent_increasing :
    IsIncreasing aspectOrientationCertainEvent := by
  intro first second _ _
  exact Set.mem_univ second

lemma aspectOrientationAbsentEvent_increasing :
    IsIncreasing aspectOrientationAbsentEvent := by
  intro first second hle hfirst
  have hcoordinate := hle s(0, 1)
  change first s(0, 1) = true at hfirst
  change second s(0, 1) = true
  rw [hfirst] at hcoordinate
  exact Bool.eq_true_of_true_le hcoordinate

lemma aspectOrientationCounterexample_isFKG :
    IsFKG (Measure.dirac aspectOrientationCounterexampleConfig) :=
  isFKG_dirac aspectOrientationCounterexampleConfig

@[simp] lemma aspectOrientationCertainEvent_measureReal :
    (Measure.dirac aspectOrientationCounterexampleConfig).real
        aspectOrientationCertainEvent = 1 := by
  rw [Measure.real, Measure.dirac_apply' _
    aspectOrientationCertainEvent_measurable]
  simp [aspectOrientationCertainEvent]

@[simp] lemma aspectOrientationAbsentEvent_measureReal :
    (Measure.dirac aspectOrientationCounterexampleConfig).real
        aspectOrientationAbsentEvent = 0 := by
  rw [Measure.real, Measure.dirac_apply' _
    aspectOrientationAbsentEvent_measurable]
  simp [aspectOrientationAbsentEvent, aspectOrientationCounterexampleConfig]

/-- No-go: it is false that every FKG measure satisfies `μ.real A ≤ μ.real B` for all measurable
increasing events `A` and `B`. -/
theorem not_fkg_implies_increasing_event_orientation_comparison :
    ¬ (∀ (mu : Measure (ConfigSpace (Sym2 (Fin 2)))), IsFKG mu →
      ∀ A B : Set (ConfigSpace (Sym2 (Fin 2))),
        MeasurableSet A → MeasurableSet B →
        IsIncreasing A → IsIncreasing B →
        mu.real A ≤ mu.real B) := by
  intro hcomparison
  have hle := hcomparison
    (Measure.dirac aspectOrientationCounterexampleConfig)
    aspectOrientationCounterexample_isFKG
    aspectOrientationCertainEvent aspectOrientationAbsentEvent
    aspectOrientationCertainEvent_measurable
    aspectOrientationAbsentEvent_measurable
    aspectOrientationCertainEvent_increasing
    aspectOrientationAbsentEvent_increasing
  rw [aspectOrientationCertainEvent_measureReal,
    aspectOrientationAbsentEvent_measureReal] at hle
  norm_num at hle

end StatMech.FK.PeriodicPlanar
