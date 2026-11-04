/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.FarDartContour
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton

/-!
# Tests for `MathlibExt.Probability.Percolation.FarDartContour`

For the all-closed configuration (origin cluster `{0}`) and `R = 0`:
* `fdc_rightExitIdx` and `fdc_leftExitIdx` are `0`, so the far exit darts are the exit darts;
* `fdc_FarReanchors` holds (with zero iterations), so it is satisfiable;
* `fdc_farExitDartsSameOrbit` and `fdc_exitDartsSameOrbit` apply with every hypothesis
  discharged (interface connectivity of a single site is `ifc_interfaceConnected`).
-/

@[expose] public section

open SimpleGraph StatMech StatMech.Lattice StatMech.Percolation

namespace MathlibExtTest.StatMech.Probability.Percolation.FarDartContour

/-- The all-closed configuration. -/
def allClosed : ConfigSpace (Sym2 (Site 2)) := fun _ => false

theorem cluster_allClosed : cluster 2 allClosed (origin 2) = {origin 2} := by
  ext y
  simp only [mem_cluster, Set.mem_singleton_iff]
  constructor
  · rintro ⟨w⟩
    cases w with
    | nil => rfl
    | cons h _ => exact absurd h.2 (by simp [allClosed])
  · rintro rfl
    exact connected_refl _ _

theorem hfin : (cluster 2 allClosed (origin 2)).Finite := by
  rw [cluster_allClosed]; exact Set.finite_singleton _

theorem hbox : cluster 2 allClosed (origin 2) ⊆ box 2 0 := by
  rw [cluster_allClosed, Set.singleton_subset_iff]
  intro i
  simp [origin]

theorem exitIndex_allClosed : exitIndex (ω := allClosed) hfin = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero (Nat.find_min' _ ?_)
  change axisSite (0 + 1) ∉ cluster 2 allClosed (origin 2)
  rw [cluster_allClosed, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp [axisSite, origin] at this

theorem leftExitIndex_allClosed : leftExitIndex (ω := allClosed) hfin = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero (Nat.find_min' _ ?_)
  change leftAxisSite (0 + 1) ∉ cluster 2 allClosed (origin 2)
  rw [cluster_allClosed, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp [leftAxisSite, origin] at this

theorem rightExitIdx_allClosed : fdc_rightExitIdx (ω := allClosed) hfin 0 = 0 :=
  Nat.eq_zero_of_le_zero (fdc_rightExitIdx_le hfin 0)

theorem leftExitIdx_allClosed : fdc_leftExitIdx (ω := allClosed) hfin 0 = 0 :=
  Nat.eq_zero_of_le_zero (fdc_leftExitIdx_le hfin 0)

/-- `fdc_FarReanchors` holds for the all-closed configuration: the far exit darts are the exit
darts. -/
theorem farReanchors_allClosed : fdc_FarReanchors allClosed hfin 0 := by
  refine ⟨⟨0, ?_⟩, ⟨0, ?_⟩⟩
  · refine Dart.ext ?_ ?_ <;>
      simp [fdc_farExitDart, exitIndex_allClosed, rightExitIdx_allClosed]
  · refine Dart.ext ?_ ?_ <;>
      simp [fdc_farLeftExitDart, leftExitIndex_allClosed, leftExitIdx_allClosed]

theorem interfaceConnected_allClosed : InterfaceConnected (cluster 2 allClosed (origin 2)) := by
  rw [cluster_allClosed]; exact ifc_interfaceConnected _

example : ∃ n : ℕ, (dartNext (cluster 2 allClosed (origin 2)))^[n]
    (fdc_farExitDart (ω := allClosed) hfin 0) = fdc_farLeftExitDart (ω := allClosed) hfin 0 :=
  fdc_farExitDartsSameOrbit hfin interfaceConnected_allClosed 0 hbox

/-- All hypotheses of `fdc_exitDartsSameOrbit` hold for the all-closed configuration. -/
example : ExitDartsSameOrbit allClosed hfin :=
  fdc_exitDartsSameOrbit hfin interfaceConnected_allClosed 0 hbox farReanchors_allClosed

end MathlibExtTest.StatMech.Probability.Percolation.FarDartContour
