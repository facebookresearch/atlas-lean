/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Probability.Percolation.OutermostContour

/-!
# Tests for `MathlibExt.Probability.Percolation.OutermostContour`

* `outC_upEdgeConfig`: its origin cluster contains `(0, 1)` and is contained in
  `{(0, 0), (0, 1)}`; the refutation `not_forall_pcFar_ExitHeadsFar` uses it.
* `outC_exitHead_mem_exterior_iff` at `R = 0` and the far-axis condition
  `outC_FarAxisHeadsFar` (proved for every finite cluster) on the up-edge configuration.
* The up-edge configuration violates `pcFar_ExitHeadsFar`, via
  `outC_pcFarExitHeadsFar_forces_eq`.
-/

@[expose] public section

open SimpleGraph StatMech StatMech.Lattice StatMech.Percolation

namespace MathlibExtTest.StatMech.Probability.Percolation.OutermostContour

example : (![0, 1] : Site 2) ∈ cluster 2 outC_upEdgeConfig (origin 2) :=
  outC_upEdgeConfig_up_mem

example : (![1, 0] : Site 2) ∉ cluster 2 outC_upEdgeConfig (origin 2) := by
  intro h
  rcases outC_upEdgeConfig_cluster_subset h with h | h
  · have := congrFun h 0; simp [origin] at this
  · have := congrFun h 0; simp at this

theorem hfin : (cluster 2 outC_upEdgeConfig (origin 2)).Finite :=
  (Set.toFinite _).subset outC_upEdgeConfig_cluster_subset

/-- Every exit head is outside `[0, 0]²`. -/
example : (exitDart (ω := outC_upEdgeConfig) hfin).head ∈ exterior 2 0 :=
  (outC_exitHead_mem_exterior_iff hfin 0).mpr (Nat.zero_le _)

/-- The far-axis condition holds for the up-edge configuration. -/
example : outC_FarAxisHeadsFar outC_upEdgeConfig hfin :=
  outC_farAxisHeadsFar_discharge hfin

/-- The up-edge configuration violates `pcFar_ExitHeadsFar`: the condition forces the box
radius to be the exit index `0`, but `(0, 1)` is in the cluster. -/
example : ¬ pcFar_ExitHeadsFar outC_upEdgeConfig hfin := by
  intro h
  obtain ⟨R, hRe, -, hbox⟩ := outC_pcFarExitHeadsFar_forces_eq hfin h
  have hidx : exitIndex (ω := outC_upEdgeConfig) hfin = 0 := by
    classical
    refine Nat.eq_zero_of_le_zero (Nat.find_min' _ ?_)
    intro hmem
    rcases outC_upEdgeConfig_cluster_subset hmem with h | h
    · have := congrFun h 0; simp [axisSite, origin] at this
    · have := congrFun h 0; simp [axisSite] at this
  have := hbox outC_upEdgeConfig_up_mem 1
  rw [hidx] at this
  simp at this

end MathlibExtTest.StatMech.Probability.Percolation.OutermostContour
