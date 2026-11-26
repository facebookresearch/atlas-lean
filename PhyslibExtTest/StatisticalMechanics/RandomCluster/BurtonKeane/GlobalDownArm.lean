/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalDownArm

/-!
# Tests for `PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalDownArm`

* In the all-closed configuration of `ℤ²` the data `bc31_TfreeDownArmData` hold for any rank, so
  `bc31_Tcount_le_boundary_of_TfreeDownArmData` gives the counting bound (non-vacuity).
* `bc31_globalCut_infinite_of_singleCut_Tfree` with `T = ∅` as a conditional statement.
* The data cannot hold for every configuration of `ℤ` (refutation through
  `tfc_not_forall_Tcount_le_boundary`).
-/

@[expose] public section

namespace PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalDownArm

open _root_.StatMech _root_.StatMech.Lattice _root_.StatMech.Percolation _root_.StatMech.Walls

/-- In the all-closed configuration every cluster is a single site, so no site is a
trifurcation. -/
theorem not_isTrifurcation_closed {d : ℕ} (x : Site d) :
    ¬ IsTrifurcation d (fun _ => false) x := by
  rintro ⟨a, -, -, -, -, ⟨h, -, -⟩, -⟩
  have hb : openSubgraph d (fun _ => false) = ⊥ := by ext; simp
  have hc : cluster d (fun _ => false) a = {a} := by
    ext y
    simp [cluster, Connected, hb, eq_comm]
  exact h (hc ▸ Set.finite_singleton a)

/-- Trifurcation-free down-arm data in the all-closed configuration. -/
theorem closed_TfreeDownArmData (d n : ℕ) (rank : Site d → ℕ ×ₗ ℕ) :
    bc31_TfreeDownArmData (d := d) (fun _ => false) n rank :=
  ⟨id, fun x _ hx => absurd hx (not_isTrifurcation_closed x),
    fun x _ hx => absurd hx (not_isTrifurcation_closed x)⟩

-- The counting bound in the all-closed configuration.
example : Tcount 2 (fun _ => false) 2 ≤ boxSV_boundaryCard 2 2 :=
  bc31_Tcount_le_boundary_of_TfreeDownArmData _ 2 (by norm_num) (fun _ => toLex (0, 0))
    (fun x _ hx => absurd hx (not_isTrifurcation_closed x)) (closed_TfreeDownArmData 2 2 _)

-- An arm avoiding the removed set stays infinite.
example (ω : ConfigSpace (Sym2 (Site 2))) (x a : Site 2)
    (hinf : (cluster 2 (removeSite x ω) a).Infinite) :
    (cluster 2 (removeSites ∅ ω) a).Infinite :=
  bc31_globalCut_infinite_of_singleCut_Tfree ω hinf fun _ _ => Finset.notMem_empty _

-- No configuration-wide down-arm data with injective ranks exist in `ℤ`.
example : ¬ ∀ (ω : ConfigSpace (Sym2 (Site 1))) (n : ℕ), 1 ≤ n →
    bc31_TfreeDownArmData ω n (fun z => toLex ((z 0).toNat, (-z 0).toNat)) :=
  fun h => tfc_not_forall_Tcount_le_boundary le_rfl fun ω n hn =>
    bc31_Tcount_le_boundary_of_TfreeDownArmData ω n hn _
      (fun x _ _ y _ _ hxy _ hr => hxy (by
        have h1 := congrArg (fun p => (ofLex p).1) hr
        have h2 := congrArg (fun p => (ofLex p).2) hr
        simp only [ofLex_toLex] at h1 h2
        funext i; rw [Subsingleton.elim i 0]; omega))
      (h ω n hn)

end PhyslibExtTest.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalDownArm
