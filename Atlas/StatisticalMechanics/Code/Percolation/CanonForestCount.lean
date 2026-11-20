/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.BoxSurfaceVolume
import Code.Lattice.Clusters
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Percolation.TrifurcationCount
import Code.Percolation.SpanForestArmsClose
import Code.Percolation.ArmReachComponentClose
import Code.Percolation.CanonicalTrifCount
import Code.Percolation.OpenSpanningForestClose

open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}




noncomputable instance cfc_boxFintype (d n : ℕ) : Fintype (↑(box d n) : Type) :=
  (box_finite d n).fintype


noncomputable def cfc_emb (d n : ℕ) : (↑(box d (n + 1)) : Type) ↪ Site d :=
  ⟨Subtype.val, Subtype.val_injective⟩


noncomputable def cfc_Gbox (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph (↑(box d (n + 1)) : Type) :=
  (openSubgraph d ω).induce (box d (n + 1))


noncomputable def cfc_F (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph (↑(box d (n + 1)) : Type) :=
  osf_spanForest (cfc_Gbox ω n)


noncomputable def cfc_T (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : SimpleGraph (Site d) :=
  (cfc_F ω n).map (cfc_emb d n)


theorem cfc_T_acyclic (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : (cfc_T ω n).IsAcyclic :=
  spc_map_acyclic (osf_spanForest_acyclic (cfc_Gbox ω n)) _


theorem cfc_T_open (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (u v : Site d)
    (h : (cfc_T ω n).Adj u v) : (openSubgraph d ω).Adj u v := by
  rw [cfc_T, SimpleGraph.map_adj] at h
  obtain ⟨p, q, hpq, rfl, rfl⟩ := h
  exact osf_spanForest_le (cfc_Gbox ω n) hpq


theorem cfc_T_support (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (u v : Site d)
    (h : (cfc_T ω n).Adj u v) : u ∈ box d (n + 1) := by
  rw [cfc_T, SimpleGraph.map_adj] at h
  obtain ⟨p, q, hpq, rfl, rfl⟩ := h
  exact p.2



theorem cfc_induce_reachable_of_walk (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∀ {a b : Site d} (w : (openSubgraph d ω).Walk a b),
      (∀ v ∈ w.support, v ∈ box d (n + 1)) →
      ∀ (ha : a ∈ box d (n + 1)) (hb : b ∈ box d (n + 1)),
        (cfc_Gbox ω n).Reachable ⟨a, ha⟩ ⟨b, hb⟩ := by
  intro a b w
  induction w with
  | nil => intro _ ha hb; exact Reachable.refl _
  | @cons u v c hadj w' ih =>
    intro hsupp hu hc
    have hv : v ∈ box d (n + 1) := hsupp v (by simp [Walk.support_cons])
    have hw'supp : ∀ z ∈ w'.support, z ∈ box d (n + 1) := fun z hz => hsupp z (by
      rw [Walk.support_cons]; exact List.mem_cons_of_mem _ hz)
    have hadj' : (cfc_Gbox ω n).Adj ⟨u, hu⟩ ⟨v, hv⟩ := hadj
    exact hadj'.reachable.trans (ih hw'supp hv hc)



theorem cfc_map_reachable (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {a b : (↑(box d (n + 1)) : Type)} (h : (cfc_F ω n).Reachable a b) :
    (cfc_T ω n).Reachable (a : Site d) (b : Site d) := by
  obtain ⟨w⟩ := h
  induction w with
  | nil => exact Reachable.refl _
  | @cons u v c hadj w' ih =>
    have hadj' : (cfc_T ω n).Adj (u : Site d) (v : Site d) := by
      rw [cfc_T, SimpleGraph.map_adj]; exact ⟨u, v, hadj, rfl, rfl⟩
    exact hadj'.reachable.trans ih



theorem cfc_removeSite_walk_to_ambient (ω : ConfigSpace (Sym2 (Site d))) (x : Site d)
    {a b : Site d} (w : (openSubgraph d (removeSite x ω)).Walk a b) :
    ∃ w' : (openSubgraph d ω).Walk a b, w'.support = w.support := by
  have hle : ∀ u v, (openSubgraph d (removeSite x ω)).Adj u v → (openSubgraph d ω).Adj u v := by
    intro u v hadj
    obtain ⟨hadj1, hopen⟩ := hadj
    refine ⟨hadj1, ?_⟩
    by_cases hx : x ∈ s(u, v)
    · rw [removeSite_apply_of_mem hx] at hopen; exact absurd hopen (by simp)
    · rwa [removeSite_apply_of_notMem hx] at hopen
  let f : (openSubgraph d (removeSite x ω)) →g (openSubgraph d ω) :=
    { toFun := id, map_rel' := fun {p q} hpq => hle p q hpq }
  refine ⟨w.map f, ?_⟩
  calc (w.map f).support = List.map (⇑f) w.support := SimpleGraph.Walk.support_map f w
    _ = List.map id w.support := by rfl
    _ = w.support := List.map_id _





theorem cfc_x_reaches_z (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a z : Site d} (hxbox : x ∈ box d n)
    (hadjxa : (openSubgraph d ω).Adj x a)
    (w : (openSubgraph d (removeSite x ω)).Walk a z) (hwx : x ∉ w.support)
    (hwbox : ∀ v ∈ w.support, v ∈ box d (n + 1)) :
    (cfc_T ω n).Reachable x z := by
  obtain ⟨w', hw'supp⟩ := cfc_removeSite_walk_to_ambient ω x w
  have hxbox1 : x ∈ box d (n + 1) := box_subset_succ d n hxbox
  set hpath : (openSubgraph d ω).Walk x z := Walk.cons hadjxa w' with hpathdef
  have hpath_box : ∀ v ∈ hpath.support, v ∈ box d (n + 1) := by
    intro v hv
    rw [hpathdef, Walk.support_cons, List.mem_cons] at hv
    rcases hv with rfl | hv
    · exact hxbox1
    · exact hwbox v (hw'supp ▸ hv)
  have hz_box : z ∈ box d (n + 1) := by
    have : z ∈ w.support := w.end_mem_support
    exact hwbox z this
  have hreach_box : (cfc_Gbox ω n).Reachable ⟨x, hxbox1⟩ ⟨z, hz_box⟩ :=
    cfc_induce_reachable_of_walk ω n hpath hpath_box hxbox1 hz_box
  have hreach_F : (cfc_F ω n).Reachable ⟨x, hxbox1⟩ ⟨z, hz_box⟩ :=
    osf_spanForest_reachable_of (cfc_Gbox ω n) hreach_box
  exact cfc_map_reachable ω n hreach_F




theorem cfc_extract_arm {T : SimpleGraph (Site d)} {x z : Site d}
    (h : T.Reachable x z) (hxz : x ≠ z) :
    ∃ (c : Site d) (rest : T.Walk c z), T.Adj x c ∧ x ∉ rest.support := by
  obtain ⟨w⟩ := h
  obtain ⟨p, hpp⟩ := w.toPath
  cases p with
  | nil => exact absurd rfl hxz
  | @cons _ c _ hadj rest =>
    refine ⟨c, rest, hadj, ?_⟩
    rw [SimpleGraph.Walk.isPath_def, SimpleGraph.Walk.support_cons, List.nodup_cons] at hpp
    exact hpp.1





theorem cfc_per_arm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x a z : Site d} (hxbox : x ∈ box d n)
    (hadjxa : (openSubgraph d ω).Adj x a)
    (w : (openSubgraph d (removeSite x ω)).Walk a z) (hwx : x ∉ w.support)
    (hwbox : ∀ v ∈ w.support, v ∈ box d (n + 1)) (hzx : z ≠ x) :
    ∃ c : Site d, (cfc_T ω n).Adj x c ∧
      (∃ wt : (cfc_T ω n).Walk c z, x ∉ wt.support) ∧
      Connected d (removeSite x ω) c z := by
  have hreach : (cfc_T ω n).Reachable x z := cfc_x_reaches_z ω n hxbox hadjxa w hwx hwbox
  have hxz : x ≠ z := fun h => hzx h.symm
  obtain ⟨c, rest, hadjxc, hrestx⟩ := cfc_extract_arm hreach hxz
  refine ⟨c, hadjxc, ⟨rest, hrestx⟩, ?_⟩
  exact sfa_walk_avoid_connected ω (cfc_T ω n) (cfc_T_open ω n) rest hrestx





theorem cfc_walk_crossing_confined {V : Type*} (G : SimpleGraph V) (p : V → Prop)
    {x y : V} (w : G.Walk x y) (hx0 : p x) (hy0 : ¬ p y) :
    ∃ a b, G.Adj a b ∧ p a ∧ ¬ p b ∧
        ∃ wxa : G.Walk x a, ∀ v ∈ wxa.support, p v := by
  classical
  induction w with
  | nil => exact absurd hx0 hy0
  | @cons u v z hadj w' ih =>
    by_cases hv : p v
    · obtain ⟨a, b, hab, ha, hb, wva, hwva⟩ := ih hv hy0
      refine ⟨a, b, hab, ha, hb, Walk.cons hadj wva, ?_⟩
      intro ww hw
      rw [Walk.support_cons, List.mem_cons] at hw
      rcases hw with rfl | hw
      · exact hx0
      · exact hwva ww hw
    · refine ⟨u, v, hadj, hx0, hv, Walk.nil, ?_⟩
      intro ww hw; rw [Walk.support_nil, List.mem_singleton] at hw; rw [hw]; exact hx0







theorem cfc_arm_reaches_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (x a : Site d) (hax : a ≠ x) (habox : a ∈ box d n)
    (hinf : (cluster d (removeSite x ω) a).Infinite) :
    ∃ z ∈ vertexBoundary d n,
      ∃ w : (openSubgraph d (removeSite x ω)).Walk a z, x ∉ w.support ∧
        ∀ v ∈ w.support, v ∈ box d n := by
  classical
  obtain ⟨y, hybox, hyconn⟩ := (cluster_infinite_iff (removeSite x ω) a).mp hinf n
  obtain ⟨w⟩ := hyconn
  obtain ⟨b, c, hbc, hb, hc, wab, hwab⟩ :=
    cfc_walk_crossing_confined (openSubgraph d (removeSite x ω)) (fun v => v ∈ box d n) w habox
      hybox
  have hblat : (hypercubicLattice d).Adj b c := (openSubgraph_le (removeSite x ω)) hbc
  refine ⟨b, tfc_boundary_cross_vertex n hn b c hb hc hblat, wab,
    arc_walk_avoids_x hax wab, hwab⟩












theorem cfc_neighbour_outside_box_imp_boundary {n : ℕ} (hn : 1 ≤ n) {x c : Site d}
    (hx : x ∈ box d n) (hadj : (hypercubicLattice d).Adj x c) (hc : c ∉ box d n) :
    x ∉ box d (n - 1) := by
  rw [hypercubicLattice_adj] at hadj
  rw [mem_box] at hx hc
  simp only [not_forall, not_le] at hc
  obtain ⟨i, hi⟩ := hc
  rw [mem_box]; simp only [not_forall, not_le]
  refine ⟨i, ?_⟩
  have hcoord : (x i - c i).natAbs ≤ 1 := by
    have hle : (x i - c i).natAbs ≤ ∑ j, (x j - c j).natAbs :=
      Finset.single_le_sum (f := fun j => (x j - c j).natAbs)
        (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
    omega
  have := hx i
  omega












theorem cfc_trif_data (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    {x : Site d} (hxbox : x ∈ box d n)
    (c0 : Fin 3 → Site d)
    (hadj : ∀ i, (openSubgraph d ω).Adj x (c0 i))
    (hne : ∀ i, c0 i ≠ x)
    (hcbox : ∀ i, c0 i ∈ box d n)
    (hcut : ¬ Connected d (removeSite x ω) (c0 0) (c0 1) ∧
            ¬ Connected d (removeSite x ω) (c0 0) (c0 2) ∧
            ¬ Connected d (removeSite x ω) (c0 1) (c0 2))
    (hinf : ∀ i, (cluster d (removeSite x ω) (c0 i)).Infinite) :
    ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
      (∀ i, (cfc_T ω n).Adj x (c i)) ∧
      (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
       ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
       ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
      (∀ i, zr i ∈ vertexBoundary d n ∧
        ∃ w : (cfc_T ω n).Walk (c i) (zr i), x ∉ w.support) := by
  classical
  have hreach : ∀ i, ∃ z ∈ vertexBoundary d n,
      ∃ w : (openSubgraph d (removeSite x ω)).Walk (c0 i) z, x ∉ w.support ∧
        ∀ v ∈ w.support, v ∈ box d n := fun i =>
    cfc_arm_reaches_boundary ω n hn x (c0 i) (hne i) (hcbox i) (hinf i)
  choose z hzb w hwx hwbox using hreach
  have hwbox1 : ∀ i, ∀ v ∈ (w i).support, v ∈ box d (n + 1) := fun i v hv =>
    box_subset_succ d n (hwbox i v hv)
  have hzx : ∀ i, z i ≠ x := by
    intro i hzix
    exact (hwx i) (hzix ▸ (w i).end_mem_support)
  have hper : ∀ i, ∃ c : Site d, (cfc_T ω n).Adj x c ∧
      (∃ wt : (cfc_T ω n).Walk c (z i), x ∉ wt.support) ∧
      Connected d (removeSite x ω) c (z i) := fun i =>
    cfc_per_arm ω n hxbox (hadj i) (w i) (hwx i) (hwbox1 i) (hzx i)
  choose c hadjxc htail hconn using hper
  
  have hzc0 : ∀ i, Connected d (removeSite x ω) (c0 i) (z i) := fun i => ⟨w i⟩
  
  have hcc0 : ∀ i, Connected d (removeSite x ω) (c i) (c0 i) := fun i =>
    (hconn i).trans (hzc0 i).symm
  
  have hcutc : ¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
      ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
      ¬ Connected d (removeSite x ω) (c 1) (c 2) := by
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact hcut.1 ((hcc0 0).symm.trans (h.trans (hcc0 1)))
    · intro h; exact hcut.2.1 ((hcc0 0).symm.trans (h.trans (hcc0 2)))
    · intro h; exact hcut.2.2 ((hcc0 1).symm.trans (h.trans (hcc0 2)))
  exact ⟨c, z, hadjxc, hcutc, fun i => ⟨hzb i, htail i⟩⟩








theorem cfc_armForestReaching_of_canonical_armsInBox
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n)
    (hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x) :
    sfa_ArmForestReaching ω n := by
  classical
  have harms : arc_TrifArmsRemoveSiteInfinite ω n :=
    ctc2_armsRemoveSiteInfinite_of_canonical ω n hcanon
  have hdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∃ (c : Fin 3 → Site d) (zr : Fin 3 → Site d),
        (∀ i, (cfc_T ω n).Adj x (c i)) ∧
        (¬ Connected d (removeSite x ω) (c 0) (c 1) ∧
         ¬ Connected d (removeSite x ω) (c 0) (c 2) ∧
         ¬ Connected d (removeSite x ω) (c 1) (c 2)) ∧
        (∀ i, zr i ∈ vertexBoundary d n ∧
          ∃ w : (cfc_T ω n).Walk (c i) (zr i), x ∉ w.support) := by
    intro x hxbox htri
    obtain ⟨c0, hadj, hne, hcut, hinf⟩ := harms x hxbox htri
    have hcbox : ∀ i, c0 i ∈ box d n := fun i =>
      harmbox x hxbox htri (c0 i) (hadj i) (hinf i)
    exact cfc_trif_data ω n hn hxbox c0 hadj hne hcbox hcut hinf
  choose! c zr hcadj hccut hcreach using hdata
  set B : Set (Site d) := vertexBoundary d n with hBdef
  obtain ⟨x0, hx0box, hx0tri⟩ := hexists
  have hc0reach := hcreach x0 hx0box hx0tri
  obtain ⟨hz0, w0, hw0x⟩ := hc0reach 0
  obtain ⟨hz1, w1, hw1x⟩ := hc0reach 1
  have hcut01 := (hccut x0 hx0box hx0tri).1
  obtain ⟨hxsurv, _, _⟩ :=
    sfa_onBPath_of_arms ω (cfc_T ω n) (cfc_T_open ω n) B
      (hcadj x0 hx0box hx0tri 0) (hcadj x0 hx0box hx0tri 1)
      w0 hw0x hz0 w1 hw1x hz1 hcut01
  refine ⟨boxFinsetBK d (n + 1), cfc_T ω n, Classical.decRel _, B, c, zr,
    cfc_T_acyclic ω n, cfc_T_open ω n, ?_, le_refl _, ⟨x0, hxsurv⟩, ?_⟩
  · intro u v huv
    rw [boxFinsetBK, Set.Finite.mem_toFinset]
    exact cfc_T_support ω n u v huv
  · intro x hxbox htri
    exact ⟨hcadj x hxbox htri, hccut x hxbox htri, hcreach x hxbox htri⟩




theorem cfc_Tcount_le_boundary_of_no_trif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  classical
  have h0 : Tcount d ω n = 0 := by
    unfold Tcount
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro x hx
    rw [boxFinsetBK, Set.Finite.mem_toFinset] at hx
    exact hno x hx
  rw [h0]
  exact Nat.zero_le _













theorem cfc_Tcount_le_boundary_of_canonical (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (hn : 1 ≤ n)
    (hcanon : ∀ x, x ∈ box d n → IsTrifurcation d ω x → IsCanonicalTrifurcation d ω x)
    (harmbox : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      ∀ a, (openSubgraph d ω).Adj x a → (cluster d (removeSite x ω) a).Infinite → a ∈ box d n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  classical
  by_cases hexists : ∃ x, x ∈ box d n ∧ IsTrifurcation d ω x
  · exact sfa_Tcount_le_boundary_of_armForestReaching ω n
      (cfc_armForestReaching_of_canonical_armsInBox ω n hn hcanon harmbox hexists)
  · simp only [not_exists, not_and] at hexists
    exact cfc_Tcount_le_boundary_of_no_trif ω n hexists

end Percolation

end StatMech
