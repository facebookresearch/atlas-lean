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

/-!
# Cut separation of trifurcation arms

Removing all trifurcations at once separates the selected arms, which gives disjoint boundary arm
ends and the trifurcation count.

## i. Overview

`daep_cutArmEnds ω n x a` is the set of boundary sites reached from `a` after `x` is removed;
`removeSites T ω` closes every edge touching `T`. Global cut separation (`daep_GlobalCutSeparation`)
chooses an infinite arm for every trifurcation such that the arms of distinct trifurcations are
disconnected after all trifurcations are removed. Their boundary arm ends are then disjoint
(`daep_CutDisjointArmEnds`), giving distinct arm ends and `Tcount ≤ |∂B_n|`.

No certificate of this kind can hold for every configuration: each one yields the
trifurcation-to-boundary injection `tfc_DistinctArmEnds`, and `tfc_not_forall_distinctArmEnds` shows
that this injection fails for some configuration in every dimension `d ≥ 1` (in `tfc_lineConfig`
every site is a trifurcation in the sense of `IsTrifurcation`). The certificate is useful
configuration by configuration; the deterministic counting bound is the reusable content.

## ii. Key results

- `daep_cutArmEnds_disjoint_of_disconnected` : disconnected arms have disjoint boundary ends
- `daep_Tcount_le_boundary_of_cutDisjoint` : disjoint arm ends bound the count
- `daep_cutDisjoint_of_globalCutSeparation` : global cut separation gives disjoint arm ends
- `daep_Tcount_le_boundary_of_globalCutSeparation` : the counting bound

## iii. Table of contents

- A. Definitions
- B. Results

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

/-! ## A. Definitions -/

open Classical in
/-- Boundary sites of `B_n` reached from `a` once `x` is removed. -/
noncomputable def daep_cutArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x a : Site d) :
    Finset (Site d) :=
  (tfc_boundaryFinset d n).filter (fun z => Connected d (removeSite x ω) a z)

/-! ## B. Results -/

lemma daep_mem_cutArmEnds {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x a z : Site d} :
    z ∈ daep_cutArmEnds ω n x a ↔ z ∈ vertexBoundary d n ∧ Connected d (removeSite x ω) a z := by
  classical
  rw [daep_cutArmEnds, Finset.mem_filter, tfc_mem_boundaryFinset]

lemma daep_cutArmEnds_subset (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x a : Site d) :
    daep_cutArmEnds ω n x a ⊆ tfc_boundaryFinset d n := by
  classical
  exact Finset.filter_subset _ _

lemma daep_cutArmEnds_disjoint_of_disconnected (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a₁ a₂ : Site d} (hdis : ¬ Connected d (removeSite x ω) a₁ a₂) :
    Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₂) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_cutArmEnds] at hw1 hw2
  exact hdis (hw1.2.trans hw2.2.symm)

lemma daep_cutArmEnds_nonempty (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x a : Site d) (habox : a ∈ box d n) (hinf : (cluster d (removeSite x ω) a).Infinite) :
    (daep_cutArmEnds ω n x a).Nonempty := by
  classical
  obtain ⟨z, hzb, hzc⟩ := bk2_branch_reaches_boundary_rem ω n hn x a habox hinf
  exact ⟨z, daep_mem_cutArmEnds.mpr ⟨hzb, hzc⟩⟩

lemma daep_three_cut_blocks_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    {x a₁ a₂ a₃ : Site d}
    (ha1box : a₁ ∈ box d n) (ha2box : a₂ ∈ box d n) (ha3box : a₃ ∈ box d n)
    (hi1 : (cluster d (removeSite x ω) a₁).Infinite)
    (hi2 : (cluster d (removeSite x ω) a₂).Infinite)
    (hi3 : (cluster d (removeSite x ω) a₃).Infinite)
    (hd12 : ¬ Connected d (removeSite x ω) a₁ a₂)
    (hd13 : ¬ Connected d (removeSite x ω) a₁ a₃)
    (hd23 : ¬ Connected d (removeSite x ω) a₂ a₃) :
    ((daep_cutArmEnds ω n x a₁).Nonempty ∧ (daep_cutArmEnds ω n x a₂).Nonempty ∧
      (daep_cutArmEnds ω n x a₃).Nonempty) ∧
    (daep_cutArmEnds ω n x a₁ ⊆ tfc_boundaryFinset d n ∧
      daep_cutArmEnds ω n x a₂ ⊆ tfc_boundaryFinset d n ∧
      daep_cutArmEnds ω n x a₃ ⊆ tfc_boundaryFinset d n) ∧
    (Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₂) ∧
      Disjoint (daep_cutArmEnds ω n x a₁) (daep_cutArmEnds ω n x a₃) ∧
      Disjoint (daep_cutArmEnds ω n x a₂) (daep_cutArmEnds ω n x a₃)) :=
  ⟨⟨daep_cutArmEnds_nonempty ω n hn x a₁ ha1box hi1,
    daep_cutArmEnds_nonempty ω n hn x a₂ ha2box hi2,
    daep_cutArmEnds_nonempty ω n hn x a₃ ha3box hi3⟩,
   ⟨daep_cutArmEnds_subset ω n x a₁, daep_cutArmEnds_subset ω n x a₂,
    daep_cutArmEnds_subset ω n x a₃⟩,
   ⟨daep_cutArmEnds_disjoint_of_disconnected ω n hd12,
    daep_cutArmEnds_disjoint_of_disconnected ω n hd13,
    daep_cutArmEnds_disjoint_of_disconnected ω n hd23⟩⟩

lemma daep_doubleCut_le (ω : ConfigSpace (Sym2 (Site d))) (x y : Site d) :
    removeSite x (removeSite y ω) ≤ ω := by
  intro e
  unfold removeSite
  by_cases hx : x ∈ e
  · simp [hx]
  · by_cases hy : y ∈ e <;> simp [hx, hy]

lemma daep_doubleCut_arms_disjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x y a b : Site d}
    (hdis : ¬ Connected d (removeSite x (removeSite y ω)) a b) :
    Disjoint (daep_cutArmEnds (removeSite y ω) n x a)
      (daep_cutArmEnds (removeSite x ω) n y b) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_cutArmEnds] at hw1 hw2
  have hsymm : removeSite y (removeSite x ω) = removeSite x (removeSite y ω) := by
    funext e
    unfold removeSite
    by_cases hx : x ∈ e <;> by_cases hy : y ∈ e <;> simp [hx, hy]
  have hwa : Connected d (removeSite x (removeSite y ω)) a w := hw1.2
  have hwb : Connected d (removeSite x (removeSite y ω)) b w := by
    rw [← hsymm]; exact hw2.2
  exact hdis (hwa.trans hwb.symm)

/-- Disjoint arm ends for `B_n`: each trifurcation gets a nonempty set of boundary sites it is
connected to, and distinct trifurcations get disjoint sets. -/
def daep_CutDisjointArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ A : Site d → Finset (Site d),
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → (A x).Nonempty) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ z ∈ A x, z ∈ vertexBoundary d n ∧ Connected d ω x z) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n →
      IsTrifurcation d ω y → x ≠ y → Disjoint (A x) (A y))

lemma daep_distinctArmEnds_of_cutDisjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep_CutDisjointArmEnds ω n) :
    tfc_DistinctArmEnds ω n := by
  classical
  obtain ⟨A, hne, hmem, hdisj⟩ := h
  set sel : Site d → Site d := fun x =>
    if hx : x ∈ box d n ∧ IsTrifurcation d ω x then (hne x hx.1 hx.2).choose else x with hsel
  refine ⟨sel, ?_, ?_⟩
  · intro x hxbox htri
    have hchoose := (hne x hxbox htri).choose_spec
    have := hmem x hxbox htri _ hchoose
    simp only [hsel, dite_eq_left (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x)]
    exact this
  · intro x hxbox htri y hybox htriy hxy
    by_contra hne'
    have hxchoose := (hne x hxbox htri).choose_spec
    have hychoose := (hne y hybox htriy).choose_spec
    simp only [hsel, dite_eq_left (⟨hxbox, htri⟩ : x ∈ box d n ∧ IsTrifurcation d ω x),
      dite_eq_left (⟨hybox, htriy⟩ : y ∈ box d n ∧ IsTrifurcation d ω y)] at hxy
    have hmem' : (hne x hxbox htri).choose ∈ A x ∩ A y :=
      Finset.mem_inter.mpr ⟨hxchoose, hxy ▸ hychoose⟩
    rw [Finset.disjoint_iff_inter_eq_empty.mp (hdisj x hxbox htri y hybox htriy hne')] at hmem'
    exact absurd hmem' (Finset.notMem_empty _)

lemma daep_Tcount_le_boundary_of_cutDisjoint (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : daep_CutDisjointArmEnds ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  tfc_Tcount_le_boundary_of_distinctArmEnds ω n (daep_distinctArmEnds_of_cutDisjoint ω n h)

lemma daep_cutDisjoint_of_subsingleton (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hsub : ∀ x y, x ∈ box d n → IsTrifurcation d ω x → y ∈ box d n →
      IsTrifurcation d ω y → x = y) :
    daep_CutDisjointArmEnds ω n := by
  classical
  refine ⟨bk2_armEndFinset ω n, ?_, ?_, ?_⟩
  · intro x hxbox htri
    exact bk2_armEndFinset_nonempty ω n hn x hxbox htri
  · intro x _ _ z hz
    exact bk2_mem_armEndFinset.mp hz
  · intro x hxbox htri y hybox htriy hxy
    exact absurd (hsub x y hxbox htri hybox htriy) hxy

lemma daep_cutDisjoint_of_disjointArmEnds (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (hdisj : bk2_DisjointArmEnds ω n) :
    daep_CutDisjointArmEnds ω n := by
  classical
  refine ⟨bk2_armEndFinset ω n, ?_, ?_, ?_⟩
  · intro x hxbox htri
    exact bk2_armEndFinset_nonempty ω n hn x hxbox htri
  · intro x _ _ z hz
    exact bk2_mem_armEndFinset.mp hz
  · intro x hxbox htri y hybox htriy hxy
    exact hdisj x hxbox htri y hybox htriy hxy

/-- The configuration `ω` with every edge touching a site of `T` closed. -/
noncomputable def removeSites (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    ConfigSpace (Sym2 (Site d)) :=
  fun e => if ∃ t ∈ T, t ∈ e then false else ω e

lemma daep_removeSites_le (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites T ω ≤ ω := by
  intro e
  unfold removeSites
  by_cases h : ∃ t ∈ T, t ∈ e <;> simp [h]

open Classical in
/-- Boundary sites of `B_n` reached from `a` once all sites of `T` are removed. -/
noncomputable def daep_globalCutArmEnds (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (a : Site d) : Finset (Site d) :=
  (tfc_boundaryFinset d n).filter (fun z => Connected d (removeSites T ω) a z)

lemma daep_mem_globalCutArmEnds {T : Finset (Site d)} {ω : ConfigSpace (Sym2 (Site d))}
    {n : ℕ} {a z : Site d} :
    z ∈ daep_globalCutArmEnds T ω n a ↔
      z ∈ vertexBoundary d n ∧ Connected d (removeSites T ω) a z := by
  classical
  rw [daep_globalCutArmEnds, Finset.mem_filter, tfc_mem_boundaryFinset]

lemma daep_globalCutArmEnds_connected (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) {a z : Site d} (hz : z ∈ daep_globalCutArmEnds T ω n a) : Connected d ω a z :=
  connected_mono (daep_removeSites_le T ω) (daep_mem_globalCutArmEnds.mp hz).2

lemma daep_globalCutArmEnds_disjoint_of_disconnected (T : Finset (Site d))
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) {a₁ a₂ : Site d}
    (hdis : ¬ Connected d (removeSites T ω) a₁ a₂) :
    Disjoint (daep_globalCutArmEnds T ω n a₁) (daep_globalCutArmEnds T ω n a₂) := by
  classical
  rw [Finset.disjoint_left]
  intro w hw1 hw2
  rw [daep_mem_globalCutArmEnds] at hw1 hw2
  exact hdis (hw1.2.trans hw2.2.symm)

lemma daep_infinite_reaches_boundary (ω' : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (a : Site d) (habox : a ∈ box d n) (hinf : (cluster d ω' a).Infinite) :
    ∃ z ∈ vertexBoundary d n, Connected d ω' a z := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff ω' a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨c, e, hce, hc, he, hr⟩ :=
    tfc_walk_crossing (openSubgraph d ω') (fun v => v ∈ box d n) w habox hybox
  have hclat : (hypercubicLattice d).Adj c e := (openSubgraph_le ω') hce
  exact ⟨c, tfc_boundary_cross_vertex n hn c e hc he hclat, hr⟩

lemma daep_globalCutArmEnds_nonempty (T : Finset (Site d)) (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (a : Site d) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSites T ω) a).Infinite) :
    (daep_globalCutArmEnds T ω n a).Nonempty := by
  classical
  obtain ⟨z, hzb, hzc⟩ := daep_infinite_reaches_boundary (removeSites T ω) n hn a habox hinf
  exact ⟨z, daep_mem_globalCutArmEnds.mpr ⟨hzb, hzc⟩⟩

/-- Global cut separation for `B_n`: each trifurcation has an arm site whose cluster stays infinite
after all trifurcations are removed, and the arm sites of distinct trifurcations are then
disconnected. -/
def daep_GlobalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → ¬ Connected d (removeSites (tfc_trifFinset ω n) ω) (b x) (b y))

lemma daep_cutDisjoint_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hn : 1 ≤ n) (h : daep_GlobalCutSeparation ω n) :
    daep_CutDisjointArmEnds ω n := by
  classical
  obtain ⟨b, hb, hsep⟩ := h
  refine ⟨fun x => daep_globalCutArmEnds (tfc_trifFinset ω n) ω n (b x), ?_, ?_, ?_⟩
  · intro x hxbox htri
    obtain ⟨hbbox, _, hbinf⟩ := hb x hxbox htri
    exact daep_globalCutArmEnds_nonempty (tfc_trifFinset ω n) ω n hn (b x) hbbox hbinf
  · intro x hxbox htri z hz
    obtain ⟨_, hbconn, _⟩ := hb x hxbox htri
    refine ⟨(daep_mem_globalCutArmEnds.mp hz).1, ?_⟩
    exact hbconn.trans (daep_globalCutArmEnds_connected (tfc_trifFinset ω n) ω n hz)
  · intro x hxbox htri y hybox htriy hxy
    exact daep_globalCutArmEnds_disjoint_of_disconnected (tfc_trifFinset ω n) ω n
      (hsep x hxbox htri y hybox htriy hxy)

lemma daep_removeSites_singleton (x : Site d) (ω : ConfigSpace (Sym2 (Site d))) :
    removeSites {x} ω = removeSite x ω := by
  funext e
  unfold removeSites removeSite
  by_cases h : x ∈ e
  · rw [ite_eq_left ⟨x, Finset.mem_singleton_self x, h⟩, ite_eq_left h]
  · rw [ite_eq_right (by rintro ⟨t, ht, hte⟩; rw [Finset.mem_singleton] at ht; exact h (ht ▸ hte)),
      ite_eq_right h]

lemma daep_globalCutSeparation_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    daep_GlobalCutSeparation ω n := by
  refine ⟨id, ?_, ?_⟩
  · intro x hxbox htri; exact absurd htri (hno x hxbox)
  · intro x hxbox htri _ _ _ _; exact absurd htri (hno x hxbox)

lemma daep_globalCutSeparation_of_uniqueTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ a : Site d} (hx0box : x₀ ∈ box d n) (htri0 : IsTrifurcation d ω x₀)
    (habox : a ∈ box d n) (haconn : Connected d ω x₀ a)
    (hainf : (cluster d (removeSite x₀ ω) a).Infinite)
    (huniq : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀) :
    daep_GlobalCutSeparation ω n := by
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
  · intro x hxbox htri y hybox htriy hxy
    exact absurd ((huniq x hxbox htri).trans (huniq y hybox htriy).symm) hxy

lemma daep_Tcount_le_boundary_of_globalCutSeparation (ω : ConfigSpace (Sym2 (Site d)))
    (n : ℕ) (hn : 1 ≤ n) (h : daep_GlobalCutSeparation ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  daep_Tcount_le_boundary_of_cutDisjoint ω n (daep_cutDisjoint_of_globalCutSeparation ω n hn h)

end Percolation

end StatMech
