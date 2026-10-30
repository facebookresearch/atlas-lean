/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib
public import PhyslibExt.StatisticalMechanics.RandomCluster.BurtonKeane.OriginCorridors

/-!
# The upper-lines configuration

Open horizontal lines at all heights `h ≥ 1` give a planar configuration with infinitely many
infinite clusters in which no three of them can be routed to the origin by disjoint corridors.

## i. Overview

`bc60_upperLines` opens exactly the horizontal edges at heights `h ≥ 1`. Each line is an infinite
cluster, and open walks keep their height, so the clusters are pairwise distinct and `N = ∞`. Three
lines meet `B_3`, so the configuration lies in `threeMeetBox 2 3`. Any opened corridor from the
neighbours of the origin joins arms that reach the first line, so disjoint corridors do not exist
(`bc60_not_hasDisjointCorridors`). This refutes the corridor hypothesis in `ℤ²`.

## ii. Key results

- `bc60_height_invariant` : open walks keep their height
- `bc60_numInfiniteClusters_top` : `bc60_upperLines` has infinitely many infinite clusters
- `bc60_mem_threeMeetBox` : it lies in `threeMeetBox 2 3`
- `bc60_not_hasDisjointCorridors` : disjoint corridors fail at `n = 3`
- `bc60_status` : the statements together

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
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation


/-! ## A. Definitions -/

open Classical in
/-- The configuration with exactly the horizontal edges at heights `h ≥ 1` open. -/
noncomputable def bc60_upperLines : ConfigSpace (Sym2 (Site 2)) :=
  fun e => if (∃ (k : ℤ) (h : ℤ), 1 ≤ h ∧ e = s(bc57_pt k h, bc57_pt (k + 1) h)) then true else false

/-! ## B. Results -/

lemma bc60_open (k : ℤ) {h : ℤ} (hh : 1 ≤ h) :
    bc60_upperLines s(bc57_pt k h, bc57_pt (k + 1) h) = true := by
  classical
  rw [bc60_upperLines, ite_eq_left]; exact ⟨k, h, hh, rfl⟩

lemma bc60_removeSite_mono (G : Finset (Sym2 (Site 2))) :
    removeSite 0 bc60_upperLines ≤ removeSite 0 (forceOpenFinset G bc60_upperLines) := by
  intro e
  unfold removeSite
  by_cases h : (0 : Site 2) ∈ e
  · simp [h]
  · simp only [h, ite_false]; exact forceOpenFinset_le G bc60_upperLines e

lemma bc60_connected_forceOpen {G : Finset (Sym2 (Site 2))} {x y : Site 2}
    (h : Connected 2 (removeSite 0 bc60_upperLines) x y) :
    Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) x y :=
  connected_mono (bc60_removeSite_mono G) h

lemma bc60_pt_eq_origin_iff {a b : ℤ} : bc57_pt a b = (0 : Site 2) ↔ a = 0 ∧ b = 0 := by
  rw [bc59_origin_eq]
  constructor
  · intro h
    have h0 := congrArg (fun f => f 0) h
    have h1 := congrArg (fun f => f 1) h
    simp only [bc57_pt_fst, bc57_pt_snd] at h0 h1
    exact ⟨h0, h1⟩
  · rintro ⟨ha, hb⟩; rw [ha, hb]

lemma bc60_open_edge_heights {u v : Site 2}
    (hopen : bc60_upperLines s(u, v) = true) : 1 ≤ u 1 ∧ 1 ≤ v 1 ∧ u 1 = v 1 := by
  classical
  rw [bc60_upperLines] at hopen
  by_cases hk : ∃ (k : ℤ) (h : ℤ), 1 ≤ h ∧ s(u, v) = s(bc57_pt k h, bc57_pt (k + 1) h)
  · obtain ⟨k, h, hh, hkeq⟩ := hk
    rw [Sym2.eq_iff] at hkeq
    rcases hkeq with ⟨hu', hv'⟩ | ⟨hu', hv'⟩
    · rw [hu', hv', bc57_pt_snd, bc57_pt_snd]; exact ⟨hh, hh, rfl⟩
    · rw [hu', hv', bc57_pt_snd, bc57_pt_snd]; exact ⟨hh, hh, rfl⟩
  · rw [ite_eq_right hk] at hopen; exact absurd hopen (by decide)

lemma bc60_line1_reach_pos (j : ℕ) :
    Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt 0 1) (bc57_pt (j : ℤ) 1) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 1)
  | succ i ih =>
    have h0 : (0 : Site 2) ∉ s(bc57_pt (i : ℤ) 1, bc57_pt ((i : ℤ) + 1) 1) := by
      rw [Sym2.mem_iff]
      rintro (h | h) <;> exact absurd (bc60_pt_eq_origin_iff.mp h.symm).2 (by decide)
    have hopen : (removeSite 0 bc60_upperLines) s(bc57_pt (i : ℤ) 1, bc57_pt ((i : ℤ) + 1) 1) = true := by
      rw [removeSite_apply_of_notMem h0]; exact bc60_open (i : ℤ) (by norm_num)
    have step : Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt (i : ℤ) 1)
        (bc57_pt ((i : ℤ) + 1) 1) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (i : ℤ) 1, hopen⟩
    have hcast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step

lemma bc60_line1_reach_neg (j : ℕ) :
    Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt 0 1) (bc57_pt (-(j : ℤ)) 1) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 1)
  | succ i ih =>
    have hadj : (hypercubicLattice 2).Adj (bc57_pt (-((i : ℤ)) - 1) 1) (bc57_pt (-((i : ℤ)) - 1 + 1) 1) :=
      bc57_pt_adj _ 1
    have heq : (-((i : ℤ)) - 1 + 1) = -((i : ℤ)) := by ring
    have h0 : (0 : Site 2) ∉ s(bc57_pt (-((i : ℤ)) - 1) 1, bc57_pt (-((i : ℤ)) - 1 + 1) 1) := by
      rw [Sym2.mem_iff]
      rintro (h | h) <;> exact absurd (bc60_pt_eq_origin_iff.mp h.symm).2 (by decide)
    have hopen : (removeSite 0 bc60_upperLines) s(bc57_pt (-((i : ℤ)) - 1) 1, bc57_pt (-((i : ℤ)) - 1 + 1) 1) = true := by
      rw [removeSite_apply_of_notMem h0]; exact bc60_open (-((i : ℤ)) - 1) (by norm_num)
    have step0 := IsOpenEdge.connected (d := 2) ⟨hadj, hopen⟩
    rw [heq] at step0
    have step : Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt (-((i : ℤ))) 1)
        (bc57_pt (-((i : ℤ)) - 1) 1) := step0.symm
    have hcast : (-(((i + 1 : ℕ)) : ℤ)) = -((i : ℤ)) - 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step

lemma bc60_line1_connected_zero (m : ℤ) :
    Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt m 1) (bc57_pt 0 1) := by
  rcases le_or_gt 0 m with hm | hm
  · have : (m.toNat : ℤ) = m := Int.toNat_of_nonneg hm
    have h := bc60_line1_reach_pos m.toNat
    rw [this] at h
    exact h.symm
  · have hpos : 0 ≤ -m := by omega
    have : ((-m).toNat : ℤ) = -m := Int.toNat_of_nonneg hpos
    have h := bc60_line1_reach_neg (-m).toNat
    rw [this] at h
    have hmm : -(-m) = m := by ring
    rw [hmm] at h
    exact h.symm

lemma bc60_line1_all_connected (m m' : ℤ) :
    Connected 2 (removeSite 0 bc60_upperLines) (bc57_pt m 1) (bc57_pt m' 1) :=
  (bc60_line1_connected_zero m).trans (bc60_line1_connected_zero m').symm

lemma bc60_step_height_diff {ω : ConfigSpace (Sym2 (Site 2))} {u v : Site 2}
    (hadj : (openSubgraph 2 ω).Adj u v) :
    (u 1 - v 1).natAbs ≤ 1 := by
  have hlat : (hypercubicLattice 2).Adj u v := hadj.1
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hlat
  omega

lemma bc60_reach_height_one {ω : ConfigSpace (Sym2 (Site 2))} {u y : Site 2}
    (hu : u 1 ≤ 0) (hy : 1 ≤ y 1) (hconn : Connected 2 ω u y) :
    ∃ w : Site 2, w 1 = 1 ∧ Connected 2 ω u w := by
  obtain ⟨walk⟩ := hconn
  induction walk with
  | nil => exact absurd hy (by omega)
  | @cons a b c hab w' ih =>
    have hstep : (a 1 - b 1).natAbs ≤ 1 := bc60_step_height_diff hab
    have habConn : Connected 2 ω a b :=
      SimpleGraph.Adj.reachable (G := openSubgraph 2 ω) hab
    by_cases hb : 1 ≤ b 1
    · have hb1 : b 1 = 1 := by omega
      exact ⟨b, hb1, habConn⟩
    · have hble : b 1 ≤ 0 := by omega
      obtain ⟨w, hw1, hwconn⟩ := ih hble hy
      exact ⟨w, hw1, habConn.trans hwconn⟩

/-- The endpoints of the edges in `G`. -/
noncomputable def bc60_Gverts (G : Finset (Sym2 (Site 2))) : Finset (Site 2) :=
  G.sup (fun e => e.toFinset)

lemma bc60_mem_Gverts_left {G : Finset (Sym2 (Site 2))} {x y : Site 2}
    (h : s(x, y) ∈ G) : x ∈ bc60_Gverts G := by
  unfold bc60_Gverts
  refine Finset.mem_sup.mpr ⟨s(x, y), h, ?_⟩
  simp [Sym2.mem_toFinset]

lemma bc60_mem_Gverts_right {G : Finset (Sym2 (Site 2))} {x y : Site 2}
    (h : s(x, y) ∈ G) : y ∈ bc60_Gverts G := by
  unfold bc60_Gverts
  refine Finset.mem_sup.mpr ⟨s(x, y), h, ?_⟩
  simp [Sym2.mem_toFinset]

lemma bc60_confined_mem_insert {G : Finset (Sym2 (Site 2))} {p y : Site 2}
    (hlow : ∀ z, Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) p z → z 1 ≤ 0)
    (w : (openSubgraph 2 (removeSite 0 (forceOpenFinset G bc60_upperLines))).Walk p y) :
    y ∈ insert p (bc60_Gverts G) := by
  induction w with
  | nil => exact Finset.mem_insert_self _ _
  | @cons p b c hpb w' ih =>
    have hpbConn : Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) p b :=
      SimpleGraph.Adj.reachable
        (G := openSubgraph 2 (removeSite 0 (forceOpenFinset G bc60_upperLines))) hpb
    have hb0 : b 1 ≤ 0 := hlow b hpbConn
    obtain ⟨_, hopen⟩ := hpb
    have h0 : (0 : Site 2) ∉ s(p, b) := by
      intro hmem; rw [removeSite_apply_of_mem hmem] at hopen; exact absurd hopen (by decide)
    rw [removeSite_apply_of_notMem h0, forceOpenFinset] at hopen
    have hbmem : b ∈ bc60_Gverts G := by
      by_cases hG : s(p, b) ∈ G
      · exact bc60_mem_Gverts_right hG
      · rw [ite_eq_right hG] at hopen
        have := (bc60_open_edge_heights hopen).2.1
        omega
    have hlow' : ∀ z, Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) b z → z 1 ≤ 0 :=
      fun z hz => hlow z (hpbConn.trans hz)
    have hcmem : c ∈ insert b (bc60_Gverts G) := ih hlow'
    rcases Finset.mem_insert.mp hcmem with hc | hc
    · rw [hc]; exact Finset.mem_insert_of_mem hbmem
    · exact Finset.mem_insert_of_mem hc

lemma bc60_arm_reaches_up {G : Finset (Sym2 (Site 2))} {a : Site 2}
    (hinf : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite) :
    ∃ w : Site 2, 1 ≤ w 1 ∧ Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a w := by
  by_contra hcon
  have hlow : ∀ z, Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a z → z 1 ≤ 0 := by
    intro z hz
    by_contra hzp
    exact hcon ⟨z, by omega, hz⟩
  have hsub : cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a ⊆
      ↑(insert a (bc60_Gverts G)) := by
    intro y hy
    rw [mem_cluster] at hy
    obtain ⟨w⟩ := hy
    exact bc60_confined_mem_insert hlow w
  exact hinf ((insert a (bc60_Gverts G)).finite_toSet.subset hsub)

lemma bc60_pt_coord (v : Site 2) : v = bc57_pt (v 0) (v 1) := by
  funext i; fin_cases i <;> simp [bc57_pt]

lemma bc60_arm_reaches_line1 {G : Finset (Sym2 (Site 2))} {a : Site 2} (ha : a 1 ≤ 1)
    (hinf : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite) :
    ∃ m : ℤ, Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a (bc57_pt m 1) := by
  rcases eq_or_lt_of_le ha with ha1 | ha0
  · refine ⟨a 0, ?_⟩
    have hav : a = bc57_pt (a 0) 1 := by conv_lhs => rw [bc60_pt_coord a]
                                         rw [ha1]
    rw [← hav]
  · have ha0' : a 1 ≤ 0 := by omega
    obtain ⟨w, hw1, hwconn⟩ := bc60_arm_reaches_up hinf
    obtain ⟨v, hv1, hvconn⟩ := bc60_reach_height_one ha0' hw1 hwconn
    refine ⟨v 0, ?_⟩
    have hvv : v = bc57_pt (v 0) 1 := by conv_lhs => rw [bc60_pt_coord v]
                                         rw [hv1]
    rw [← hvv]; exact hvconn

lemma bc60_arms_connected {G : Finset (Sym2 (Site 2))} {a a' : Site 2}
    (ha : a 1 ≤ 1) (ha' : a' 1 ≤ 1)
    (hinf : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a).Infinite)
    (hinf' : (cluster 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a').Infinite) :
    Connected 2 (removeSite 0 (forceOpenFinset G bc60_upperLines)) a a' := by
  obtain ⟨m, hm⟩ := bc60_arm_reaches_line1 ha hinf
  obtain ⟨m', hm'⟩ := bc60_arm_reaches_line1 ha' hinf'
  exact (hm.trans (bc60_connected_forceOpen (bc60_line1_all_connected m m'))).trans hm'.symm

lemma bc60_line_reach_pos {h : ℤ} (hh : 1 ≤ h) (j : ℕ) :
    Connected 2 bc60_upperLines (bc57_pt 0 h) (bc57_pt (j : ℤ) h) := by
  induction j with
  | zero => simpa using connected_refl _ (bc57_pt 0 h)
  | succ i ih =>
    have step : Connected 2 bc60_upperLines (bc57_pt (i : ℤ) h) (bc57_pt ((i : ℤ) + 1) h) :=
      IsOpenEdge.connected ⟨bc57_pt_adj (i : ℤ) h, bc60_open (i : ℤ) hh⟩
    have hcast : ((i + 1 : ℕ) : ℤ) = (i : ℤ) + 1 := by push_cast; ring
    rw [hcast]; exact ih.trans step

lemma bc60_pt_outside_box (j : ℕ) (h : ℤ) : bc57_pt ((j : ℤ) + 1) h ∉ box 2 j := by
  rw [mem_box]; simp only [not_forall, not_le]; refine ⟨0, ?_⟩
  rw [bc57_pt_fst]
  have : ((j : ℤ) + 1).natAbs = (j + 1 : ℕ) := by omega
  omega

lemma bc60_cluster_infinite {h : ℤ} (hh : 1 ≤ h) :
    (cluster 2 bc60_upperLines (bc57_pt 0 h)).Infinite := by
  rw [cluster_infinite_iff]
  intro j
  refine ⟨bc57_pt ((j : ℤ) + 1) h, bc60_pt_outside_box j h, ?_⟩
  have := bc60_line_reach_pos hh (j + 1)
  have hcast : ((j + 1 : ℕ) : ℤ) = (j : ℤ) + 1 := by push_cast; ring
  rwa [hcast] at this

lemma bc60_pt_zero_mem_box {h : ℤ} {n : ℕ} (hh : h.natAbs ≤ n) : bc57_pt 0 h ∈ box 2 n := by
  rw [mem_box]; intro i; fin_cases i
  · change ((bc57_pt 0 h) 0).natAbs ≤ n; rw [bc57_pt_fst]; simp
  · change ((bc57_pt 0 h) 1).natAbs ≤ n; rw [bc57_pt_snd]; exact hh

lemma bc60_height_invariant {h : ℤ} {u y : Site 2} (hu : u 1 = h)
    (hconn : Connected 2 bc60_upperLines u y) : y 1 = h := by
  obtain ⟨w⟩ := hconn
  induction w with
  | nil => exact hu
  | @cons a b c hab w' ih =>
    obtain ⟨_, hopen⟩ := hab
    have := (bc60_open_edge_heights hopen).2.2
    exact ih (by omega)

lemma bc60_cluster_ne {h h' : ℤ} (hne : h ≠ h') :
    cluster 2 bc60_upperLines (bc57_pt 0 h) ≠ cluster 2 bc60_upperLines (bc57_pt 0 h') := by
  intro hEq
  have hmem : bc57_pt 0 h' ∈ cluster 2 bc60_upperLines (bc57_pt 0 h) := by
    rw [hEq]; exact self_mem_cluster _ _
  rw [mem_cluster] at hmem
  have hht : (bc57_pt 0 h') 1 = h := bc60_height_invariant (by rw [bc57_pt_snd]) hmem
  rw [bc57_pt_snd] at hht
  omega

lemma bc60_cluster_family_inj :
    Function.Injective (fun n : ℕ => cluster 2 bc60_upperLines (bc57_pt 0 ((n : ℤ) + 1))) := by
  intro n n' h
  by_contra hne
  exact bc60_cluster_ne (by simp only [ne_eq]; omega) h

lemma bc60_numInfiniteClusters_top : numInfiniteClusters 2 bc60_upperLines = ⊤ := by
  unfold numInfiniteClusters
  apply Set.Infinite.encard_eq
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => cluster 2 bc60_upperLines (bc57_pt 0 ((n : ℤ) + 1)))
  · intro n n' h; exact bc60_cluster_family_inj h
  · intro n
    exact ⟨bc60_cluster_infinite (by omega), bc57_pt 0 ((n : ℤ) + 1), rfl⟩

lemma bc60_mem_threeMeetBox : bc60_upperLines ∈ threeMeetBox 2 3 := by
  refine ⟨bc60_numInfiniteClusters_top,
    bc57_pt 0 1, bc57_pt 0 2, bc57_pt 0 3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact bc60_pt_zero_mem_box (by decide)
  · exact bc60_pt_zero_mem_box (by decide)
  · exact bc60_pt_zero_mem_box (by decide)
  · exact bc60_cluster_infinite (by decide)
  · exact bc60_cluster_infinite (by decide)
  · exact bc60_cluster_infinite (by decide)
  · exact bc60_cluster_ne (by decide)
  · exact bc60_cluster_ne (by decide)
  · exact bc60_cluster_ne (by decide)

lemma bc60_nbr_height_le {a : Site 2} (hadj : (hypercubicLattice 2).Adj 0 a) : a 1 ≤ 1 := by
  rw [hypercubicLattice_adj, Fin.sum_univ_two] at hadj
  simp only [Pi.zero_apply, zero_sub, Int.natAbs_neg] at hadj
  omega

lemma bc60_not_disjointCorridors : ¬ bc59_DisjointCorridors bc60_upperLines := by
  rintro ⟨G, a₁, a₂, a₃, _, _, ⟨hadj1, hadj2, _⟩, ⟨hi1, hi2, _⟩, ⟨hsep12, _, _⟩⟩
  exact hsep12 (bc60_arms_connected (bc60_nbr_height_le hadj1) (bc60_nbr_height_le hadj2) hi1 hi2)

lemma bc60_not_hasDisjointCorridors : ¬ bc59_HasDisjointCorridors 2 3 := by
  intro h
  exact bc60_not_disjointCorridors (h bc60_upperLines bc60_mem_threeMeetBox)

/-! ## C. Summary -/

lemma bc60_status :
    (bc60_upperLines ∈ threeMeetBox 2 3) ∧
    (numInfiniteClusters 2 bc60_upperLines = ⊤) ∧
    (¬ bc59_DisjointCorridors bc60_upperLines) ∧
    (¬ bc59_HasDisjointCorridors 2 3) :=
  ⟨bc60_mem_threeMeetBox, bc60_numInfiniteClusters_top,
    bc60_not_disjointCorridors, bc60_not_hasDisjointCorridors⟩

end StatMech.Walls
