/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Basic.ENNReal.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.HypercubicLattice
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.BoxSurfaceVolume
public import MathlibExt.Combinatorics.SimpleGraph.Lattice.Clusters
public import MathlibExt.Probability.Percolation.InfiniteClusterCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneUniqueness
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeaneMerge
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.TrifurcationCount
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ArmEndsDistinct
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.ForestLeafInjectionBound
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.GlobalCutSeparation

/-!
# Single-cut branch separation

If removing one trifurcation separates its arm from every other connected trifurcation's arm, the
arms are separated after removing all of them and the Burton–Keane count holds.

## i. Overview

`daep2_SingleCutBranchSeparation ω n` chooses infinite arm sites and asks that for connected `x ≠
y`, removing `x` disconnects the arm of `x` from the arm of `y`; `daep2_SameClusterCutSeparation`
asks the same within clusters. Removing more sites only disconnects more, so this gives global cut
separation and `Tcount ≤ |∂B_n|`. Branches of distinct clusters are always separated.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `daep2_globalCut_disconnected_of_singleCut` : single cuts give global separation
- `daep2_globalCutSeparation_of_sameCluster` : same-cluster separation gives global separation
- `daep2_Tcount_le_boundary_of_singleCut` : the counting bound
- `daep2_singleCutBranchSeparation_of_distinctClusters` : separation for trifurcations in distinct
  clusters

## iii. Table of contents

- A. Results

## iv. References

- R. M. Burton and M. Keane, *Density and uniqueness in percolation*, Comm. Math. Phys. 121 (1989),
  501–505.
- G. Grimmett, *Percolation*, 2nd ed., Springer (1999), §8.2.
-/

@[expose] public section

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}

/-! ## A. Results -/

lemma daep2_armEnds_share_forces_branch_connection (ω : ConfigSpace (Sym2 (Site d)))
    {x a b w : Site d}
    (hwa : Connected d (removeSite x ω) a w) (hwb : Connected d (removeSite x ω) b w) :
    Connected d (removeSite x ω) a b :=
  hwa.trans hwb.symm

lemma daep2_no_shared_boundary_of_disconnected_branches (ω : ConfigSpace (Sym2 (Site d)))
    {x a b : Site d} (hdis : ¬ Connected d (removeSite x ω) a b) :
    ∀ w, ¬ (Connected d (removeSite x ω) a w ∧ Connected d (removeSite x ω) b w) := by
  intro w ⟨hwa, hwb⟩
  exact hdis (daep2_armEnds_share_forces_branch_connection ω hwa hwb)

lemma daep2_globalCut_disconnected_of_omega_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {u v : Site d} (hdis : ¬ Connected d ω u v) :
    ¬ Connected d (removeSites T ω) u v :=
  fun hc => hdis (connected_mono (daep_removeSites_le T ω) hc)

lemma daep2_crossCluster_branches_globalCut_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x y a b : Site d}
    (hxa : Connected d ω x a) (hyb : Connected d ω y b)
    (hxy : ¬ Connected d ω x y) :
    ¬ Connected d (removeSites T ω) a b := by
  intro hc
  have hab : Connected d ω a b := connected_mono (daep_removeSites_le T ω) hc
  exact hxy (hxa.trans (hab.trans hyb.symm))

lemma daep2_removeSites_le_removeSite (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    {x : Site d} (hxT : x ∈ T) :
    removeSites T ω ≤ removeSite x ω := by
  intro e
  unfold removeSites removeSite
  by_cases hx : x ∈ e
  · rw [ite_eq_left hx, ite_eq_left ⟨x, hxT, hx⟩]
  · rw [ite_eq_right hx]
    by_cases hT : ∃ t ∈ T, t ∈ e
    · rw [ite_eq_left hT]; exact Bool.false_le _
    · rw [ite_eq_right hT]

lemma daep2_globalCut_disconnected_of_singleCut (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) {x u v : Site d} (hxT : x ∈ T)
    (hdis : ¬ Connected d (removeSite x ω) u v) :
    ¬ Connected d (removeSites T ω) u v :=
  fun hc => hdis (connected_mono (daep2_removeSites_le_removeSite T ω hxT) hc)

/-- Same-cluster cut separation for `B_n`: infinite arm sites such that for connected trifurcations
`x ≠ y` one single cut separates their arms. -/
def daep2_SameClusterCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y))

lemma daep2_globalCutSeparation_of_sameCluster (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep2_SameClusterCutSeparation ω n) :
    daep_GlobalCutSeparation ω n := by
  classical
  obtain ⟨b, hb, hsame⟩ := h
  refine ⟨b, hb, ?_⟩
  intro x hxbox htri y hybox htriy hxy
  by_cases hconn : Connected d ω x y
  · exact hsame x hxbox htri y hybox htriy hxy hconn
  · obtain ⟨_, hbxconn, _⟩ := hb x hxbox htri
    obtain ⟨_, hbyconn, _⟩ := hb y hybox htriy
    exact daep2_crossCluster_branches_globalCut_disconnected (tfc_trifFinset ω n) ω
      hbxconn hbyconn hconn

lemma daep2_meets_at_most_one_branch (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₂ v) ∧
    ¬ (Connected d (removeSite x ω) a₁ v ∧ Connected d (removeSite x ω) a₃ v) ∧
    ¬ (Connected d (removeSite x ω) a₂ v ∧ Connected d (removeSite x ω) a₃ v) :=
  ⟨fun ⟨h1, h2⟩ => hd12 (h1.trans h2.symm),
   fun ⟨h1, h3⟩ => hd13 (h1.trans h3.symm),
   fun ⟨h2, h3⟩ => hd23 (h2.trans h3.symm)⟩

lemma daep2_two_branches_avoid (ω : ConfigSpace (Sym2 (Site d)))
    {x a₁ a₂ a₃ : Site d}
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) (v : Site d) :
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₂ v) ∨
    (¬ Connected d (removeSite x ω) a₁ v ∧ ¬ Connected d (removeSite x ω) a₃ v) ∨
    (¬ Connected d (removeSite x ω) a₂ v ∧ ¬ Connected d (removeSite x ω) a₃ v) := by
  classical
  by_cases h1 : Connected d (removeSite x ω) a₁ v
  · refine Or.inr (Or.inr ⟨fun h2 => hd12 (h1.trans h2.symm), fun h3 => hd13 (h1.trans h3.symm)⟩)
  · by_cases h2 : Connected d (removeSite x ω) a₂ v
    · exact Or.inr (Or.inl ⟨h1, fun h3 => hd23 (h2.trans h3.symm)⟩)
    · exact Or.inl ⟨h1, h2⟩

/-- Single-cut branch separation for `B_n`: infinite arm sites such that for connected trifurcations
`x ≠ y`, removing `x` disconnects the arm of `x` from the arm of `y`. -/
def daep2_SingleCutBranchSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y →
      ¬ Connected d (removeSite x ω) (b x) (b y))

lemma daep2_sameClusterCutSeparation_of_singleCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep2_SingleCutBranchSeparation ω n) :
    daep2_SameClusterCutSeparation ω n := by
  obtain ⟨b, hb, hsep⟩ := h
  refine ⟨b, hb, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  exact daep2_globalCut_disconnected_of_singleCut (tfc_trifFinset ω n) ω hxT
    (hsep x hxbox htri y hybox htriy hxy hconn)

lemma daep2_sameClusterCutSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    daep2_SameClusterCutSeparation ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)

lemma daep2_sameClusterCutSeparation_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    daep2_SameClusterCutSeparation ω n := by
  classical
  have hT : tfc_trifFinset ω n = {x₀} := by
    apply Finset.eq_singleton_iff_unique_mem.mpr
    refine ⟨tfc_mem_trifFinset.mpr ⟨hx0box, htri0⟩, ?_⟩
    intro y hy
    rw [tfc_mem_trifFinset] at hy
    exact huniq y hy.1 hy.2
  have hcut : removeSites (tfc_trifFinset ω n) ω = removeSite x₀ ω := by
    rw [hT, daep_removeSites_singleton]
  refine ⟨fun _ => a, ?_, ?_⟩
  · intro x hxbox htri
    have hx0 : x = x₀ := huniq x hxbox htri
    subst hx0
    refine ⟨habox, haconn, ?_⟩
    rw [hcut]; exact hainf
  · intro x hxbox htri y hybox htriy hxy _
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy

lemma daep2_singleCutBranchSeparation_of_distinctClusters (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (b : Site d → Site d)
    (hb : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsep : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y → ¬ Connected d ω x y) :
    daep2_SingleCutBranchSeparation ω n := by
  refine ⟨b, hb, ?_⟩
  intro x hxbox htri y hybox htriy hxy hconn
  exact absurd hconn (hsep x hxbox htri y hybox htriy hxy)

lemma daep2_singleCutBranchSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    daep2_SingleCutBranchSeparation ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _ _; exact absurd htri (hno x hxbox)

lemma daep2_Tcount_le_boundary_of_sameCluster (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daep2_SameClusterCutSeparation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep_Tcount_le_boundary_of_globalCutSeparation ω n hn
    (daep2_globalCutSeparation_of_sameCluster ω n h)

lemma daep2_Tcount_le_boundary_of_singleCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daep2_SingleCutBranchSeparation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep2_Tcount_le_boundary_of_sameCluster ω n hn
    (daep2_sameClusterCutSeparation_of_singleCut ω n h)

end Percolation

end StatMech
