/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










import Code.Percolation.CanonBurtonKeane

open MeasureTheory Set
open scoped ENNReal

namespace StatMech.FrontierB

open Lattice ConfigSpace Percolation


theorem boxEdges_subset_hypercubic_edgeSet (d n : ℕ) :
    (↑(boxEdges d n) : Set (Sym2 (Site d))) ⊆
      (hypercubicLattice d).edgeSet := by
  intro e he
  induction e using Sym2.inductionOn with
  | _ x y =>
      rw [SimpleGraph.mem_edgeSet]
      exact (Percolation.mem_boxEdges_iff.mp he).2.2



theorem latticeInsertionMerge_excludes_finite_ge_two
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hfe : ∀ F : Finset (Sym2 (Site d)),
      (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet →
        μ.map (fun ω => forceOpenFinset F ω) ≪ μ)
    {k : ℕ∞} (hk : μ {ω | numInfiniteClusters d ω = k} = 1)
    (hk2 : 2 ≤ k) (hktop : k ≠ ⊤) : False := by
  obtain ⟨n, hpos⟩ := Percolation.exists_twoMeetBox_pos μ hk2 hk
  exact Percolation.merge_contradiction μ hk (boxEdges d n)
    (hfe (boxEdges d n) (boxEdges_subset_hypercubic_edgeSet d n))
    (lt_of_lt_of_le hpos
      (measure_mono (Percolation.twoMeetBox_subset_mergeWitness n k)))
    (Percolation.mergeWitness_subset_force_lt (boxEdges d n) hktop)




theorem latticeInsertion_canonical_uniqueness
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (hd : 1 ≤ d)
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (hfe : ∀ F : Finset (Sym2 (Site d)),
      (↑F : Set (Sym2 (Site d))) ⊆ (hypercubicLattice d).edgeSet →
        μ.map (fun ω => forceOpenFinset F ω) ≪ μ)
    (htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsCanonicalTrifurcation d ω 0}) :
    (μ {ω | numInfiniteClusters d ω = 0} = 1 ∨
        μ {ω | numInfiniteClusters d ω = 1} = 1) ∧
      μ (atLeastTwoInfinite d) = 0 ∧
      μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  obtain ⟨k, hktop, hk⟩ :=
    Percolation.cbk_numInfiniteClusters_ne_top μ hd herg htrif
  have hknot2 : ¬ 2 ≤ k := by
    intro hk2
    exact latticeInsertionMerge_excludes_finite_ge_two μ hfe hk hk2 hktop
  have hkle : k ≤ 1 := Percolation.enat_le_one_of_not_two hknot2
  have hsub : {ω | numInfiniteClusters d ω = k} ⊆
      (atLeastTwoInfinite d)ᶜ := by
    intro ω hω
    rw [Percolation.atLeastTwoInfinite_compl]
    simp only [Set.mem_setOf_eq] at hω ⊢
    rw [hω]
    exact hkle
  have hfull : μ (atLeastTwoInfinite d)ᶜ = 1 :=
    le_antisymm prob_le_one (hk ▸ measure_mono hsub)
  have hmerge : μ (atLeastTwoInfinite d) = 0 :=
    (prob_compl_eq_one_iff Percolation.measurableSet_atLeastTwoInfinite).mp hfull
  exact ⟨Percolation.numInfiniteClusters_zero_or_one_of_const μ hk hmerge,
    hmerge, Percolation.infiniteCluster_unique_ae μ herg hmerge⟩

end StatMech.FrontierB
