/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.ENat.Defs
public import Mathlib.Topology.Defs.Filter
public import Mathlib.Order.Filter.AtTopBot.Defs
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseTrifArms
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndDisjoint
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestPeel
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneErgodic
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.BernoulliErgodicFiniteEnergy

/-!
# Coarse trifurcations at scale zero and global forest arms

At scale zero a coarse trifurcation is a trifurcation; global forest arms bound the trifurcation
count, and uniqueness follows from ergodicity and the merge condition alone.

## i. Overview

For `L = 0` the coarse box is a single site, and a coarse trifurcation at the origin is a
trifurcation. Global forest arms (`aed_GlobalForestArms`) bound `Tcount` by the boundary size for `n
≥ 1`, and the count at `n = 0` is at most the volume. `bc25_burton_keane_uniqueness_of_forest`
concludes at most one infinite cluster from ergodicity and `μ(at least two infinite clusters) = 0`;
its forest and density hypotheses are not used.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `bc25_isTrifurcation_of_coarseTrif_zero` : coarse trifurcations at scale zero are trifurcations
- `StatMech.Percolation.aed_Tcount_le_boundary_of_globalForestArms` (in `ArmEndDisjoint`) : global
  forest arms bound the count
- `bc25_burton_keane_uniqueness_of_forest` : uniqueness from ergodicity and the merge condition

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph MeasureTheory
open scoped ENNReal NNReal Topology
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma bc25_isTrifurcation_of_coarseTrif_zero {ω : ConfigSpace (Sym2 (Site d))}
    (h : IsCoarseTrifurcation d 0 ω) : IsTrifurcation d ω (0 : Site d) := by
  obtain ⟨a₁, a₂, a₃, b₁, b₂, b₃, hne, hbox, _hadj, hconn, hinf, hsep⟩ := h
  have hbox0 : ∀ {b : Site d}, b ∈ box d 0 → b = (0 : Site d) := by
    intro b hb; rw [bc24_box_zero] at hb; simpa using hb
  have hb₁0 : b₁ = (0 : Site d) := hbox0 hbox.1
  have hb₂0 : b₂ = (0 : Site d) := hbox0 hbox.2.1
  have hb₃0 : b₃ = (0 : Site d) := hbox0 hbox.2.2
  have hbridge := bc24_removeSites_box_zero (d := d) ω
  rw [hbridge] at hinf hsep
  refine ⟨a₁, a₂, a₃, hne, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · exact (hb₁0 ▸ hconn.1).symm
    · exact (hb₂0 ▸ hconn.2.1).symm
    · exact (hb₃0 ▸ hconn.2.2).symm
  · exact ⟨hinf.1.mono (ctc2_cluster_removeSite_subset 0 a₁ ω),
      hinf.2.1.mono (ctc2_cluster_removeSite_subset 0 a₂ ω),
      hinf.2.2.mono (ctc2_cluster_removeSite_subset 0 a₃ ω)⟩
  · exact hsep

lemma bc25_coarseTrif_zero_chain {ω : ConfigSpace (Sym2 (Site d))} :
    (IsCanonicalTrifurcation d ω (0 : Site d) → IsCoarseTrifurcation d 0 ω) ∧
      (IsCoarseTrifurcation d 0 ω → IsTrifurcation d ω (0 : Site d)) :=
  ⟨bc24_coarseTrif_of_canonical_origin, bc25_isTrifurcation_of_coarseTrif_zero⟩

lemma bc25_bridge_nonvacuous :
    ∃ ω : ConfigSpace (Sym2 (Site 2)),
      IsCoarseTrifurcation 2 0 ω ∧ IsTrifurcation 2 ω (0 : Site 2) := by
  obtain ⟨ω, hω⟩ := bc24_coarseTrif_nonvacuous
  exact ⟨ω, hω, bc25_isTrifurcation_of_coarseTrif_zero hω⟩

lemma bc25_Tcount_zero_le_box (ω : ConfigSpace (Sym2 (Site d))) :
    Tcount d ω 0 ≤ (boxFinsetBK d 0).card := by
  classical
  unfold Tcount
  exact Finset.card_filter_le _ _

lemma bc25_burton_keane_uniqueness_of_forest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ]
    (herg : IsErgodic (G := Multiplicative (Site d)) μ)
    (_hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → aed_GlobalForestArms ω n)
    (_hdens : Filter.Tendsto
      (fun n => (boxSV_boundaryCard d n : ℝ) / ((boxFinsetBK d n).card : ℝ))
      Filter.atTop (nhds 0))
    (_htrif : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      0 < μ {ω | IsTrifurcation d ω 0})
    (hmerge : μ (atLeastTwoInfinite d) = 0) :
    ∃ k : ℕ∞, k ≤ 1 ∧ μ {ω | numInfiniteClusters d ω = k} = 1
      ∧ μ {ω | numInfiniteClusters d ω ≤ 1} = 1 := by
  classical
  obtain ⟨k, hk⟩ := numInfiniteClusters_ae_const μ herg
  have hknot2 : ¬ (2 ≤ k) := by
    intro h2
    have hsub : {ω | numInfiniteClusters d ω = k} ⊆ atLeastTwoInfinite d := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω
      exact (show 2 ≤ numInfiniteClusters d ω by rw [hω]; exact h2)
    have hle : μ {ω | numInfiniteClusters d ω = k} ≤ μ (atLeastTwoInfinite d) :=
      measure_mono hsub
    rw [hk, hmerge] at hle
    exact absurd hle (by norm_num)
  exact ⟨k, enat_le_one_of_not_two hknot2, hk, numInfiniteClusters_le_one_of_const μ hk hmerge⟩

end StatMech.Walls
