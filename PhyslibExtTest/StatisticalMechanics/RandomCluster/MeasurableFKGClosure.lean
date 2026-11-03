/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.MeasurableFKGClosure

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.MeasurableFKGClosure`

On configurations of `ℕ`:
* `isClopen_of_dependsOn_finset` for "coordinate `0` is open";
* `finiteUpwardHull_isIncreasing`, `finiteUpwardHull_isClopen` and `subset_finiteUpwardHull`
  for the hull over `{0, 1}` of "coordinate `0` is open";
* `fkg_measurable_of_isClopen` for a Dirac measure (which satisfies the clopen FKG hypothesis
  because its values are `0` or `1`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.MeasurableFKGClosure

open _root_.StatMech MeasureTheory

/-- The event "coordinate `0` is open". -/
def open0 : Set (ConfigSpace ℕ) := {ω | ω 0 = true}

/-- `open0` depends only on `{0}`. -/
theorem open0_dependsOn : StatMech.DependsOn open0 ((({0} : Finset ℕ)) : Set ℕ) := by
  intro x y h
  change (x 0 = true) ↔ (y 0 = true)
  rw [h 0 (by simp)]

-- A finitely supported event is clopen.
example : IsClopen open0 := isClopen_of_dependsOn_finset open0 {0} open0_dependsOn

-- The finite upward hull is a clopen increasing superset.
example : IsIncreasing (finiteUpwardHull {0, 1} open0) ∧
    IsClopen (finiteUpwardHull {0, 1} open0) ∧ open0 ⊆ finiteUpwardHull {0, 1} open0 :=
  ⟨finiteUpwardHull_isIncreasing _ _, finiteUpwardHull_isClopen _ _,
   subset_finiteUpwardHull _ _⟩

/-- A Dirac measure satisfies the FKG inequality on all measurable sets. -/
theorem dirac_fkg (x : ConfigSpace ℕ) (C D : Set (ConfigSpace ℕ)) (hC : MeasurableSet C)
    (hD : MeasurableSet D) :
    (Measure.dirac x).real C * (Measure.dirac x).real D ≤ (Measure.dirac x).real (C ∩ D) := by
  simp only [Measure.real, Measure.dirac_apply' _ hC, Measure.dirac_apply' _ hD,
    Measure.dirac_apply' _ (hC.inter hD)]
  by_cases hxC : x ∈ C <;> by_cases hxD : x ∈ D <;> simp [hxC, hxD]

-- FKG extends from clopen to measurable increasing events (Dirac measure).
example (x : ConfigSpace ℕ) :=
  fkg_measurable_of_isClopen (Measure.dirac x)
    (fun C D hC hD _ _ => dirac_fkg x C D hC.isOpen.measurableSet hD.isOpen.measurableSet)
    open0 open0 (isClopen_of_dependsOn_finset open0 {0} open0_dependsOn).isOpen.measurableSet
    (isClopen_of_dependsOn_finset open0 {0} open0_dependsOn).isOpen.measurableSet
    (fun _ _ hxy hx => by
      have h := hxy 0
      change _ = true at hx ⊢
      rw [hx] at h
      exact top_le_iff.mp h)
    (fun _ _ hxy hx => by
      have h := hxy 0
      change _ = true at hx ⊢
      rw [hx] at h
      exact top_le_iff.mp h)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.MeasurableFKGClosure
