/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.OutermostContour
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.InterfaceConnectedSingleton

/-!
# Tests for `MathlibExt.Probability.Percolation.PcFarContour`

* The per-configuration condition `pcFar_ExitHeadsFar` is satisfiable: it holds for the
  all-closed configuration, whose origin cluster is `{0}`.
* For that configuration `InterfaceConnected` holds (`ifc_interfaceConnected`), so
  `pcFar_exitDartsSameOrbit_of_far` applies with all hypotheses discharged.
* The universal form of the condition fails (`not_forall_pcFar_ExitHeadsFar`, restated); this is
  why the `∀ ω` consumers were deleted in Stage B.
-/

@[expose] public section

open SimpleGraph StatMech StatMech.Lattice StatMech.Percolation

namespace MathlibExtTest.StatMech.Probability.Percolation.PcFarContour

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

theorem exitIndex_allClosed : exitIndex (ω := allClosed) hfin = 0 := by
  classical
  refine Nat.eq_zero_of_le_zero (Nat.find_min' _ ?_)
  change axisSite (0 + 1) ∉ cluster 2 allClosed (origin 2)
  rw [cluster_allClosed, Set.mem_singleton_iff]
  intro h
  have := congrFun h 0
  simp [axisSite, origin] at this

/-- The far-exit-heads condition holds for the all-closed configuration, with `R = 0`. -/
theorem pcFar_allClosed : pcFar_ExitHeadsFar allClosed hfin := by
  refine ⟨0, ?_, (outC_exitHead_mem_exterior_iff hfin 0).mpr (Nat.zero_le _),
    (outC_leftExitHead_mem_exterior_iff hfin 0).mpr (Nat.zero_le _)⟩
  rw [cluster_allClosed, Set.singleton_subset_iff]
  intro i
  simp [origin]

theorem interfaceConnected_allClosed : InterfaceConnected (cluster 2 allClosed (origin 2)) := by
  rw [cluster_allClosed]; exact ifc_interfaceConnected _

/-- All hypotheses of `pcFar_exitDartsSameOrbit_of_far` hold for the all-closed configuration. -/
example : ExitDartsSameOrbit allClosed hfin :=
  pcFar_exitDartsSameOrbit_of_far hfin interfaceConnected_allClosed pcFar_allClosed

/-- The condition forces the two exit indices to coincide; here both are `0`. -/
example : exitIndex (ω := allClosed) hfin = leftExitIndex (ω := allClosed) hfin :=
  outC_pcFarExitHeadsFar_imp_exitIndex_eq hfin pcFar_allClosed

/-- The universal form of the condition is false. -/
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 2))) (hfin : (cluster 2 ω (origin 2)).Finite),
    pcFar_ExitHeadsFar ω hfin :=
  not_forall_pcFar_ExitHeadsFar

end MathlibExtTest.StatMech.Probability.Percolation.PcFarContour
