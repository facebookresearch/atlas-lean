/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Order.Filter.Defs
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CoarseBoundaryForest
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.CanonForestCount

/-!
# Contracted-lattice trifurcations

Removing the `L`-box around `y` gives the contracted lattice; a contracted-lattice trifurcation is
exactly a coarse trifurcation.

## i. Overview

`bc67_contractedLattice ω L y` is the open subgraph after removing the `L`-box around `y`, and
`bc67_GnIncident ω L y a` says that `a` is joined to the box by an open edge.
`bc67_IsGnTrifurcation` asks for three incident sites with infinite, pairwise unreachable clusters
in the contracted lattice; it is equivalent to `bc61_IsCoarseTrifurcation`. Infinite arms reach the
boundary of every box, and global arm forests bound the coarse count. The origin of
`bc60_upperLines` is a contracted-lattice trifurcation for `L ≥ 3`.

The trifurcation notion here is the coarse one on `L`-boxes (`bc61_IsCoarseTrifurcation`,
`bc67_IsGnTrifurcation`), whose arms are infinite after the whole `L`-box is removed. Results that
assume a certificate for every configuration are conditional: no such certificate is constructed for
all configurations.

## ii. Key results

- `bc67_coarseTrif_is_G_n_trifurcation` : contracted-lattice and coarse trifurcations agree
- `bc67_Gn_arm_reaches_boundary` : infinite arms reach the boundary
- `bc67_Gn_armForest_coarseTcount` : arm forests bound the coarse count
- `bc67_status` : the statements together

## iii. Table of contents

- A. Definitions
- B. Results
- C. Summary

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}

/-! ## A. Definitions -/

/-- `a` is joined by an open edge to a site of the `L`-box around `y`. -/
def bc67_GnIncident (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d) : Prop :=
  ∃ b ∈ bc61_boxAround d L y, (openSubgraph d ω).Adj b a

/-- The open subgraph after removing the `L`-box around `y`. -/
noncomputable def bc67_contractedLattice (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    SimpleGraph (Site d) :=
  openSubgraph d (removeSites (bc61_boxAround d L y) ω)

/-! ## B. Results -/

lemma bc67_contractedLattice_adj (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d) :
    (bc67_contractedLattice ω L y).Adj a b ↔
      (openSubgraph d (removeSites (bc61_boxAround d L y) ω)).Adj a b :=
  Iff.rfl

lemma bc67_Gn_deletion_eq_removeSites (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d) :
    (bc67_contractedLattice ω L y).Reachable a b ↔
      Connected d (removeSites (bc61_boxAround d L y) ω) a b :=
  Iff.rfl

lemma bc67_contractedLattice_le (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    bc67_contractedLattice ω L y ≤ openSubgraph d ω :=
  openSubgraph_mono (bc61_removeBox_le d L y ω)

lemma bc67_connected_of_Gn {ω : ConfigSpace (Sym2 (Site d))} {L : ℕ} {y a b : Site d}
    (h : (bc67_contractedLattice ω L y).Reachable a b) : Connected d ω a b :=
  bc61_connected_of_cut ((bc67_Gn_deletion_eq_removeSites ω L y a b).mp h)

/-- A contracted-lattice trifurcation at `y`: three sites incident to the `L`-box around `y` whose
clusters after removing the box are infinite and pairwise unreachable. -/
def bc67_IsGnTrifurcation (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) : Prop :=
  ∃ a₁ a₂ a₃ : Site d,
    (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
    ((cluster d (removeSites (bc61_boxAround d L y) ω) a₁).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₂).Infinite ∧
     (cluster d (removeSites (bc61_boxAround d L y) ω) a₃).Infinite) ∧
    (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
     ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
     ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃)

lemma bc67_gnTrif_of_coarseTrif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (h : bc61_IsCoarseTrifurcation ω L y) : bc67_IsGnTrifurcation ω L y := by
  obtain ⟨a₁, a₂, a₃, ⟨b₁, hb₁, hadj₁⟩, ⟨b₂, hb₂, hadj₂⟩, ⟨b₃, hb₃, hadj₃⟩,
    ⟨hinf₁, hinf₂, hinf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩ := h
  exact ⟨a₁, a₂, a₃,
    ⟨⟨b₁, hb₁, hadj₁⟩, ⟨b₂, hb₂, hadj₂⟩, ⟨b₃, hb₃, hadj₃⟩⟩,
    ⟨hinf₁, hinf₂, hinf₃⟩,
    ⟨hcut₁₂, hcut₁₃, hcut₂₃⟩⟩

lemma bc67_coarseTrif_of_gnTrif (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d)
    (h : bc67_IsGnTrifurcation ω L y) : bc61_IsCoarseTrifurcation ω L y := by
  obtain ⟨a₁, a₂, a₃, ⟨hin₁, hin₂, hin₃⟩, ⟨hinf₁, hinf₂, hinf₃⟩, hcut₁₂, hcut₁₃, hcut₂₃⟩ := h
  exact ⟨a₁, a₂, a₃, hin₁, hin₂, hin₃, ⟨hinf₁, hinf₂, hinf₃⟩, ⟨hcut₁₂, hcut₁₃, hcut₂₃⟩⟩

lemma bc67_coarseTrif_is_G_n_trifurcation (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d) :
    bc61_IsCoarseTrifurcation ω L y ↔ bc67_IsGnTrifurcation ω L y :=
  ⟨bc67_gnTrif_of_coarseTrif ω L y, bc67_coarseTrif_of_gnTrif ω L y⟩

lemma bc67_upperLines_is_G_n_trifurcation {L : ℕ} (hL : 3 ≤ L) :
    bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2) :=
  bc67_gnTrif_of_coarseTrif bc60_upperLines L 0 (bc61_wholeBox_severs_upperLines hL)

lemma bc67_upperLines_Gn_severs {L : ℕ} (_hL : 3 ≤ L) :
    ¬ (bc67_contractedLattice bc60_upperLines L 0).Reachable
        (bc57_pt ((L : ℤ) + 1) 1) (bc57_pt ((L : ℤ) + 1) 2) := by
  rw [bc67_Gn_deletion_eq_removeSites]
  exact bc61_upperLines_arm_disconnected (by norm_num)

lemma bc67_Gn_arm_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (hR : 1 ≤ R)
    (y a : Site d) (habox : a ∈ box d R)
    (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z := by
  obtain ⟨z, hz, hconn⟩ := bc66_coarse_armReaching_unconditional ω L R hR y a habox hinf
  exact ⟨z, hz, (bc67_Gn_deletion_eq_removeSites ω L y a z).mpr hconn⟩

lemma bc67_Gn_singleVertex_trifurcation_degree (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ)
    (y : Site d) (h : bc67_IsGnTrifurcation ω L y) :
    ∃ a₁ a₂ a₃ : Site d,
      (bc67_GnIncident ω L y a₁ ∧ bc67_GnIncident ω L y a₂ ∧ bc67_GnIncident ω L y a₃) ∧
      (¬ (bc67_contractedLattice ω L y).Reachable a₁ a₂ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₁ a₃ ∧
       ¬ (bc67_contractedLattice ω L y).Reachable a₂ a₃) := by
  obtain ⟨a₁, a₂, a₃, hincs, _, hcuts⟩ := h
  exact ⟨a₁, a₂, a₃, hincs, hcuts⟩

lemma bc67_Gn_armForest_of_forestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (ιU : Site d → W) (lamL : W → Site d)
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y))
    (hιinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
    (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
    bc65_ConnectedCoarseForest ω L R := by
  refine bc66_connectedForest_of_forestData ω L R W G ιU lamL hacyc hmin ?_ ?_ hlammap hlaminj
  · intro y hybox htri
    exact hdeg3 y hybox ((bc67_coarseTrif_is_G_n_trifurcation ω L y).mp htri)
  · intro y hybox htri z hzbox htriz hyz
    exact hιinj y hybox ((bc67_coarseTrif_is_G_n_trifurcation ω L y).mp htri)
      z hzbox ((bc67_coarseTrif_is_G_n_trifurcation ω L z).mp htriz) hyz

lemma bc67_Gn_armForest_coarseTcount (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (W : Type) [Fintype W] [Nonempty W] [DecidableEq W]
    (G : SimpleGraph W) [DecidableRel G.Adj] (ιU : Site d → W) (lamL : W → Site d)
    (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v)
    (hdeg3 : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y))
    (hιinj : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z)
    (hlammap : ∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d R)
    (hlaminj : Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc65_coarseTcount_le_boundary_of_connectedForest ω L R
    (bc67_Gn_armForest_of_forestData ω L R W G ιU lamL hacyc hmin hdeg3 hιinj hlammap hlaminj)

/-! ## C. Summary -/

lemma bc67_status :
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b : Site d),
      (bc67_contractedLattice ω L y).Reachable a b ↔
        Connected d (removeSites (bc61_boxAround d L y) ω) a b) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y : Site d),
      bc61_IsCoarseTrifurcation ω L y ↔ bc67_IsGnTrifurcation ω L y) ∧
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ), 1 ≤ R → ∀ (y a : Site d), a ∈ box d R →
      (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite →
      ∃ z ∈ vertexBoundary d R, (bc67_contractedLattice ω L y).Reachable a z) ∧
    (∀ {L : ℕ}, 3 ≤ L → bc67_IsGnTrifurcation bc60_upperLines L (0 : Site 2)) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro ω L y a b; exact bc67_Gn_deletion_eq_removeSites ω L y a b
  · intro ω L y; exact bc67_coarseTrif_is_G_n_trifurcation ω L y
  · intro ω L R hR y a habox hinf; exact bc67_Gn_arm_reaches_boundary ω L R hR y a habox hinf
  · intro L hL; exact bc67_upperLines_is_G_n_trifurcation hL

end StatMech.Walls
