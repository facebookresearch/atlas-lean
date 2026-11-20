/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Code.FK.PeriodicPlanarSheffield

















open MeasureTheory Set

namespace StatMech.FK.PeriodicPlanar


theorem isFKG_dirac {V : Type} (omega : ConfigSpace (Sym2 V)) :
    IsFKG (Measure.dirac omega) := by
  intro A B hA hB _hAi _hBi
  rw [Measure.real, Measure.real, Measure.real,
    Measure.dirac_apply' _ hA, Measure.dirac_apply' _ hB,
    Measure.dirac_apply' _ (hA.inter hB)]
  by_cases homegaA : omega ∈ A <;>
    by_cases homegaB : omega ∈ B <;>
      simp [homegaA, homegaB]


def aspectOrientationCounterexampleConfig : ConfigSpace (Sym2 (Fin 2)) :=
  fun _ => false


def aspectOrientationCertainEvent : Set (ConfigSpace (Sym2 (Fin 2))) :=
  Set.univ


def aspectOrientationAbsentEvent : Set (ConfigSpace (Sym2 (Fin 2))) :=
  {omega | omega s(0, 1) = true}

theorem aspectOrientationCertainEvent_measurable :
    MeasurableSet aspectOrientationCertainEvent :=
  MeasurableSet.univ

theorem aspectOrientationAbsentEvent_measurable :
    MeasurableSet aspectOrientationAbsentEvent := by
  have hpre : aspectOrientationAbsentEvent =
      (fun omega : ConfigSpace (Sym2 (Fin 2)) => omega s(0, 1)) ⁻¹' {true} := by
    ext omega
    simp [aspectOrientationAbsentEvent]
  rw [hpre]
  exact (measurable_pi_apply s(0, 1)) (measurableSet_singleton true)

theorem aspectOrientationCertainEvent_increasing :
    IsIncreasing aspectOrientationCertainEvent := by
  intro first second _ _
  exact Set.mem_univ second

theorem aspectOrientationAbsentEvent_increasing :
    IsIncreasing aspectOrientationAbsentEvent := by
  intro first second hle hfirst
  have hcoordinate := hle s(0, 1)
  change first s(0, 1) = true at hfirst
  change second s(0, 1) = true
  rw [hfirst] at hcoordinate
  exact Bool.eq_true_of_true_le hcoordinate

theorem aspectOrientationCounterexample_isFKG :
    IsFKG (Measure.dirac aspectOrientationCounterexampleConfig) :=
  isFKG_dirac aspectOrientationCounterexampleConfig

@[simp] theorem aspectOrientationCertainEvent_measureReal :
    (Measure.dirac aspectOrientationCounterexampleConfig).real
        aspectOrientationCertainEvent = 1 := by
  rw [Measure.real, Measure.dirac_apply' _
    aspectOrientationCertainEvent_measurable]
  simp [aspectOrientationCertainEvent]

@[simp] theorem aspectOrientationAbsentEvent_measureReal :
    (Measure.dirac aspectOrientationCounterexampleConfig).real
        aspectOrientationAbsentEvent = 0 := by
  rw [Measure.real, Measure.dirac_apply' _
    aspectOrientationAbsentEvent_measurable]
  simp [aspectOrientationAbsentEvent, aspectOrientationCounterexampleConfig]




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
  norm_num at hle

end StatMech.FK.PeriodicPlanar
