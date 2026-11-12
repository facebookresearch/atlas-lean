/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.Clusters
import Code.Lattice.PlanarTopology
import Code.Percolation.BurtonKeane
import Code.Percolation.BurtonKeaneUniqueness
import Code.Walls.bc26forest
import Code.Walls.bc33escaping

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}









def ray34_AvoidReach {V : Type*} (G : SimpleGraph V) (S : Set V) (v w : V) : Prop :=
  ∃ p : G.Walk v w, ∀ u ∈ p.support, u ∉ S


def ray34_AvoidCluster {V : Type*} (G : SimpleGraph V) (S : Set V) (v : V) : Set V :=
  {w | ray34_AvoidReach G S v w}

@[simp]
theorem ray34_mem_avoidCluster {V : Type*} {G : SimpleGraph V} {S : Set V} {v w : V} :
    w ∈ ray34_AvoidCluster G S v ↔ ray34_AvoidReach G S v w := Iff.rfl


theorem ray34_avoidReach_refl {V : Type*} (G : SimpleGraph V) (S : Set V) {v : V}
    (hv : v ∉ S) : ray34_AvoidReach G S v v :=
  ⟨Walk.nil, by intro u hu; rw [Walk.support_nil, List.mem_singleton] at hu; exact hu ▸ hv⟩


theorem ray34_avoidReach_symm {V : Type*} {G : SimpleGraph V} {S : Set V} {v w : V}
    (h : ray34_AvoidReach G S v w) : ray34_AvoidReach G S w v := by
  obtain ⟨p, hp⟩ := h
  refine ⟨p.reverse, ?_⟩
  intro u hu
  rw [Walk.support_reverse, List.mem_reverse] at hu
  exact hp u hu


theorem ray34_avoidReach_trans {V : Type*} {G : SimpleGraph V} {S : Set V} {u v w : V}
    (huv : ray34_AvoidReach G S u v) (hvw : ray34_AvoidReach G S v w) :
    ray34_AvoidReach G S u w := by
  obtain ⟨p, hp⟩ := huv
  obtain ⟨q, hq⟩ := hvw
  refine ⟨p.append q, ?_⟩
  intro x hx
  rw [Walk.support_append, List.mem_append] at hx
  rcases hx with hx | hx
  · exact hp x hx
  · exact hq x (List.mem_of_mem_tail hx)


theorem ray34_avoidCluster_avoids {V : Type*} {G : SimpleGraph V} {S : Set V} {v w : V}
    (h : w ∈ ray34_AvoidCluster G S v) : w ∉ S := by
  obtain ⟨p, hp⟩ := h
  exact hp w p.end_mem_support


theorem ray34_self_mem_avoidCluster {V : Type*} (G : SimpleGraph V) (S : Set V) {v : V}
    (hv : v ∉ S) : v ∈ ray34_AvoidCluster G S v :=
  ray34_avoidReach_refl G S hv



theorem ray34_notMem_of_avoidCluster_nonempty {V : Type*} {G : SimpleGraph V} {S : Set V} {v : V}
    (h : (ray34_AvoidCluster G S v).Nonempty) : v ∉ S := by
  obtain ⟨w, p, hp⟩ := h
  exact hp v p.start_mem_support


theorem ray34_avoidCluster_eq_of_reach {V : Type*} {G : SimpleGraph V} {S : Set V} {v w : V}
    (h : ray34_AvoidReach G S v w) : ray34_AvoidCluster G S v = ray34_AvoidCluster G S w := by
  ext z
  simp only [ray34_mem_avoidCluster]
  exact ⟨fun hz => ray34_avoidReach_trans (ray34_avoidReach_symm h) hz,
    fun hz => ray34_avoidReach_trans h hz⟩


theorem ray34_avoidCluster_mono {V : Type*} {G : SimpleGraph V} {S T : Set V} (hST : S ⊆ T)
    (v : V) : ray34_AvoidCluster G T v ⊆ ray34_AvoidCluster G S v := by
  intro w hw
  obtain ⟨p, hp⟩ := hw
  exact ⟨p, fun u hu hus => hp u hu (hST hus)⟩





theorem ray34_avoidCluster_diff_subset_biUnion {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [LocallyFinite G] {S : Set V} [DecidablePred (· ∉ S)] (v : V) :
    ray34_AvoidCluster G S v \ {v} ⊆
      ⋃ w ∈ (G.neighborFinset v).filter (· ∉ S), ray34_AvoidCluster G (insert v S) w := by
  intro z hz
  obtain ⟨hzc, hzv⟩ := hz
  simp only [Set.mem_singleton_iff] at hzv
  
  obtain ⟨p, hp⟩ := hzc
  set q := p.toPath with hq
  have hqsub : (q : G.Walk v z).support ⊆ p.support := p.support_toPath_subset
  have hqpath : (q : G.Walk v z).IsPath := q.2
  have hqavoid : ∀ u ∈ (q : G.Walk v z).support, u ∉ S := fun u hu => hp u (hqsub hu)
  
  obtain ⟨w, hadj, q', hcons⟩ := Walk.exists_eq_cons_of_ne (Ne.symm hzv) (q : G.Walk v z)
  have hqcons : (q : G.Walk v z) = Walk.cons hadj q' := hcons
  
  have hwS : w ∉ S := by
    apply hqavoid w
    rw [hqcons, Walk.support_cons]
    exact List.mem_cons.mpr (Or.inr q'.start_mem_support)
  
  have hqpath' : (Walk.cons hadj q').IsPath := hqcons ▸ hqpath
  have hvnotin : v ∉ q'.support := ((Walk.cons_isPath_iff hadj q').mp hqpath').2
  have hq'avoid : ∀ u ∈ q'.support, u ∉ insert v S := by
    intro u hu
    rw [Set.mem_insert_iff]; push Not
    refine ⟨?_, ?_⟩
    · rintro rfl; exact hvnotin hu
    · apply hqavoid u
      rw [hqcons, Walk.support_cons]
      exact List.mem_cons.mpr (Or.inr hu)
  rw [Set.mem_iUnion₂]
  refine ⟨w, ?_, ⟨q', hq'avoid⟩⟩
  rw [Finset.mem_filter, mem_neighborFinset]
  exact ⟨hadj, hwS⟩








theorem ray34_konig_step {V : Type*} [DecidableEq V] {G : SimpleGraph V} [LocallyFinite G]
    {S : Set V} {v : V} (hv : v ∉ S) (hinf : (ray34_AvoidCluster G S v).Infinite) :
    ∃ w, G.Adj v w ∧ w ∉ S ∧ w ∈ ray34_AvoidCluster G S v ∧
      (ray34_AvoidCluster G (insert v S) w).Infinite := by
  classical
  
  have hdiff : (ray34_AvoidCluster G S v \ {v}).Infinite :=
    hinf.diff (Set.finite_singleton v)
  
  have hcover := ray34_avoidCluster_diff_subset_biUnion (G := G) (S := S) v
  
  by_contra hcon
  push Not at hcon
  have hfin : ∀ w ∈ (((G.neighborFinset v).filter (· ∉ S) : Finset V) : Set V),
      (ray34_AvoidCluster G (insert v S) w).Finite := by
    intro w hw
    rw [Finset.mem_coe, Finset.mem_filter, mem_neighborFinset] at hw
    
    have hwc : w ∈ ray34_AvoidCluster G S v := by
      refine ⟨Walk.cons hw.1 Walk.nil, ?_⟩
      intro u hu
      rw [Walk.support_cons, Walk.support_nil] at hu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact hv
      · exact hw.2
    exact hcon w hw.1 hw.2 hwc
  
  have hunionfin :
      (⋃ w ∈ (((G.neighborFinset v).filter (· ∉ S) : Finset V) : Set V),
        ray34_AvoidCluster G (insert v S) w).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) hfin
  
  exact hdiff (hunionfin.subset hcover)










def ray34_KState {V : Type*} (G : SimpleGraph V) : Type _ :=
  { p : Set V × V // p.2 ∉ p.1 ∧ (ray34_AvoidCluster G p.1 p.2).Infinite }



noncomputable def ray34_kstep {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]
    (s : ray34_KState G) : ray34_KState G :=
  ⟨(insert s.1.2 s.1.1, (ray34_konig_step s.2.1 s.2.2).choose),
    ray34_notMem_of_avoidCluster_nonempty
      (ray34_konig_step s.2.1 s.2.2).choose_spec.2.2.2.nonempty,
    (ray34_konig_step s.2.1 s.2.2).choose_spec.2.2.2⟩



theorem ray34_kstep_adj {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]
    (s : ray34_KState G) : G.Adj s.1.2 (ray34_kstep G s).1.2 :=
  (ray34_konig_step s.2.1 s.2.2).choose_spec.1


theorem ray34_kstep_fst {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]
    (s : ray34_KState G) : (ray34_kstep G s).1.1 = insert s.1.2 s.1.1 := rfl









theorem ray34_konig {V : Type*} [DecidableEq V] (G : SimpleGraph V) [LocallyFinite G]
    {S : Set V} {v : V} (hv : v ∉ S) (hinf : (ray34_AvoidCluster G S v).Infinite) :
    ∃ r : ℕ → V, r 0 = v ∧ Function.Injective r ∧
      (∀ k, G.Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ S) := by
  classical
  
  set s0 : ray34_KState G := ⟨(S, v), hv, hinf⟩ with hs0
  set state : ℕ → ray34_KState G := fun n => Nat.rec s0 (fun _ s => ray34_kstep G s) n with hstate
  set r : ℕ → V := fun n => (state n).1.2 with hr
  have hstate_succ : ∀ n, state (n + 1) = ray34_kstep G (state n) := fun n => rfl
  
  have hmono : ∀ n, (state n).1.1 ⊆ (state (n + 1)).1.1 := by
    intro n
    rw [hstate_succ, ray34_kstep_fst]
    exact Set.subset_insert _ _
  have hmono_le : ∀ {m n}, m ≤ n → (state m).1.1 ⊆ (state n).1.1 := by
    intro m n hmn
    induction hmn with
    | refl => exact subset_rfl
    | step h ih => exact ih.trans (hmono _)
  have hScontained : ∀ n, S ⊆ (state n).1.1 := by
    intro n
    have h0 : (state 0).1.1 = S := rfl
    have := hmono_le (Nat.zero_le n)
    rwa [h0] at this
  
  have hnotin : ∀ n, r n ∉ (state n).1.1 := fun n => (state n).2.1
  
  have hravoid : ∀ n, r n ∉ S := fun n hn => hnotin n (hScontained n hn)
  
  have hr_in_later : ∀ {m n}, m < n → r m ∈ (state n).1.1 := by
    intro m n hmn
    have hm1 : m + 1 ≤ n := hmn
    have : r m ∈ (state (m + 1)).1.1 := by
      rw [hstate_succ, ray34_kstep_fst]; exact Set.mem_insert _ _
    exact hmono_le hm1 this
  
  have hinj : Function.Injective r := by
    intro a b hab
    by_contra hne
    rcases Nat.lt_or_ge a b with h | h
    · 
      exact hnotin b (hab ▸ hr_in_later h)
    · rcases lt_of_le_of_ne h (Ne.symm hne) with h'
      exact hnotin a (hab.symm ▸ hr_in_later h')
  refine ⟨r, rfl, hinj, ?_, hravoid⟩
  intro k
  have := ray34_kstep_adj G (state k)
  rwa [← hstate_succ k] at this










open Classical in



theorem ray34_avoidCluster_diff_subset_biUnion_gen {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [LocallyFinite G] {S : Set V} (v t : V) :
    ray34_AvoidCluster G S v \ {t} ⊆
      ray34_AvoidCluster G (insert t S) v ∪
      ⋃ w ∈ (G.neighborFinset t).filter (· ∉ insert t S),
        ray34_AvoidCluster G (insert t S) w := by
  intro z hz
  obtain ⟨hzc, hzt⟩ := hz
  simp only [Set.mem_singleton_iff] at hzt
  obtain ⟨p, hp⟩ := hzc
  set q := p.toPath with hq
  have hqsub : (q : G.Walk v z).support ⊆ p.support := p.support_toPath_subset
  have hqpath : (q : G.Walk v z).IsPath := q.2
  have hqavoid : ∀ u ∈ (q : G.Walk v z).support, u ∉ S := fun u hu => hp u (hqsub hu)
  by_cases htq : t ∈ (q : G.Walk v z).support
  · 
    right
    set qd := (q : G.Walk v z).dropUntil t htq with hqd
    have hqdsub : qd.support ⊆ (q : G.Walk v z).support := (q : G.Walk v z).support_dropUntil_subset htq
    
    have hqdavoid : ∀ u ∈ qd.support, u ∉ S := fun u hu => hqavoid u (hqdsub hu)
    have hqdpath : qd.IsPath := hqpath.dropUntil htq
    
    obtain ⟨w, hadj, q', hcons⟩ := Walk.exists_eq_cons_of_ne (Ne.symm hzt) qd
    have hqdcons : qd = Walk.cons hadj q' := hcons
    have hqdpath' : (Walk.cons hadj q').IsPath := hqdcons ▸ hqdpath
    have hvnotin : t ∉ q'.support := ((Walk.cons_isPath_iff hadj q').mp hqdpath').2
    have hwS : w ∉ S := by
      apply hqdavoid w
      rw [hqdcons, Walk.support_cons]
      exact List.mem_cons.mpr (Or.inr q'.start_mem_support)
    have hq'avoid : ∀ u ∈ q'.support, u ∉ insert t S := by
      intro u hu
      rw [Set.mem_insert_iff]; push Not
      refine ⟨?_, ?_⟩
      · rintro rfl; exact hvnotin hu
      · apply hqdavoid u
        rw [hqdcons, Walk.support_cons]
        exact List.mem_cons.mpr (Or.inr hu)
    rw [Set.mem_iUnion₂]
    refine ⟨w, ?_, ⟨q', hq'avoid⟩⟩
    rw [Finset.mem_filter, mem_neighborFinset, Set.mem_insert_iff]
    push Not
    exact ⟨hadj, fun heq => (hadj.ne heq.symm).elim, hwS⟩
  · 
    left
    refine ⟨(q : G.Walk v z), ?_⟩
    intro u hu
    rw [Set.mem_insert_iff]; push Not
    refine ⟨?_, hqavoid u hu⟩
    rintro rfl; exact htq hu




theorem ray34_root_mem_of_piece_meets {V : Type*} {G : SimpleGraph V} {S : Set V} {t v w z : V}
    (hz1 : z ∈ ray34_AvoidCluster G (insert t S) w) (hz2 : z ∈ ray34_AvoidCluster G S v) :
    w ∈ ray34_AvoidCluster G S v := by
  have hwz : ray34_AvoidReach G S w z :=
    ray34_avoidCluster_mono (Set.subset_insert t S) w hz1
  exact ray34_avoidReach_trans hz2 (ray34_avoidReach_symm hwz)






theorem ray34_avoidCluster_step {V : Type*} [DecidableEq V] {G : SimpleGraph V} [LocallyFinite G]
    {S : Set V} {v : V} (hinf : (ray34_AvoidCluster G S v).Infinite) (t : V) :
    ∃ b, b ∈ ray34_AvoidCluster G S v ∧ (ray34_AvoidCluster G (insert t S) b).Infinite := by
  classical
  
  have hvS : v ∉ S := ray34_notMem_of_avoidCluster_nonempty hinf.nonempty
  have hvc : v ∈ ray34_AvoidCluster G S v := ray34_self_mem_avoidCluster G S hvS
  have hdiff : (ray34_AvoidCluster G S v \ {t}).Infinite := hinf.diff (Set.finite_singleton t)
  have hcover := ray34_avoidCluster_diff_subset_biUnion_gen (G := G) (S := S) v t
  by_contra hcon
  push Not at hcon
  
  set C := ray34_AvoidCluster G S v with hC
  
  have hvfin : (ray34_AvoidCluster G (insert t S) v ∩ C).Finite :=
    (hcon v hvc).inter_of_left C
  
  have hfin : ∀ w ∈ (((G.neighborFinset t).filter (· ∉ insert t S) : Finset V) : Set V),
      (ray34_AvoidCluster G (insert t S) w ∩ C).Finite := by
    intro w _
    rcases (ray34_AvoidCluster G (insert t S) w ∩ C).eq_empty_or_nonempty with he | hne
    · rw [he]; exact Set.finite_empty
    · obtain ⟨z, hz1, hz2⟩ := hne
      have hwc : w ∈ C := ray34_root_mem_of_piece_meets hz1 hz2
      exact (hcon w hwc).inter_of_left C
  
  have hsub : ray34_AvoidCluster G S v \ {t} ⊆
      (ray34_AvoidCluster G (insert t S) v ∩ C) ∪
      ⋃ w ∈ (((G.neighborFinset t).filter (· ∉ insert t S) : Finset V) : Set V),
        (ray34_AvoidCluster G (insert t S) w ∩ C) := by
    intro z hz
    have hzC : z ∈ C := hz.1
    have := hcover hz
    rw [Set.mem_union, Set.mem_iUnion₂] at this ⊢
    rcases this with h | ⟨w, hw, hwz⟩
    · exact Or.inl ⟨h, hzC⟩
    · exact Or.inr ⟨w, hw, hwz, hzC⟩
  have hunionfin :
      ((ray34_AvoidCluster G (insert t S) v ∩ C) ∪
        ⋃ w ∈ (((G.neighborFinset t).filter (· ∉ insert t S) : Finset V) : Set V),
          (ray34_AvoidCluster G (insert t S) w ∩ C)).Finite :=
    hvfin.union (Set.Finite.biUnion (Finset.finite_toSet _) hfin)
  exact hdiff (hunionfin.subset hsub)







theorem ray34_infinite_avoidCluster_of_finset {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    [LocallyFinite G] {v : V} (hinf : (ray34_AvoidCluster G ∅ v).Infinite) (T : Finset V) :
    ∃ b, b ∈ ray34_AvoidCluster G ∅ v ∧ (ray34_AvoidCluster G (↑T) b).Infinite := by
  classical
  induction T using Finset.induction with
  | empty => exact ⟨v, ray34_self_mem_avoidCluster G ∅ (by simp), by simpa using hinf⟩
  | @insert t T' htT' ih =>
    obtain ⟨b, hb1, hb2⟩ := ih
    obtain ⟨b', hb'1, hb'2⟩ := ray34_avoidCluster_step hb2 t
    refine ⟨b', ?_, ?_⟩
    · 
      have hbb' : ray34_AvoidReach G ∅ b b' :=
        ray34_avoidCluster_mono (Set.empty_subset (↑T')) b hb'1
      exact ray34_avoidReach_trans hb1 hbb'
    · 
      rw [Finset.coe_insert]; exact hb'2









noncomputable instance ray34_locallyFinite_openSubgraph (ω : ConfigSpace (Sym2 (Site d))) :
    SimpleGraph.LocallyFinite (openSubgraph d ω) := by
  classical
  intro x
  apply Fintype.ofFinset
    (((hypercubicLattice d).neighborFinset x).filter (fun y => (openSubgraph d ω).Adj x y))
  intro y
  rw [Finset.mem_filter, SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborFinset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩



theorem ray34_avoidCluster_empty_eq_cluster (ω : ConfigSpace (Sym2 (Site d))) (v : Site d) :
    ray34_AvoidCluster (openSubgraph d ω) ∅ v = cluster d ω v := by
  ext w
  simp only [ray34_mem_avoidCluster, mem_cluster]
  constructor
  · rintro ⟨p, _⟩; exact p.reachable
  · rintro ⟨p⟩; exact ⟨p, fun u _ => Set.notMem_empty u⟩


theorem ray34_connected_of_avoidReach {ω : ConfigSpace (Sym2 (Site d))} {S : Set (Site d)}
    {v w : Site d} (h : ray34_AvoidReach (openSubgraph d ω) S v w) : Connected d ω v w :=
  h.choose.reachable





theorem ray34_Tavoiding_ray_of_infinite_cluster (ω : ConfigSpace (Sym2 (Site d))) {v : Site d}
    (hinf : (cluster d ω v).Infinite) (T : Finset (Site d)) :
    ∃ b : Site d, Connected d ω v b ∧
      ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧
        (∀ k, (openSubgraph d ω).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ T) := by
  classical
  
  have hinf' : (ray34_AvoidCluster (openSubgraph d ω) ∅ v).Infinite := by
    rw [ray34_avoidCluster_empty_eq_cluster]; exact hinf
  
  obtain ⟨b, hbmem, hbinf⟩ := ray34_infinite_avoidCluster_of_finset hinf' T
  have hbconn : Connected d ω v b := by
    rw [ray34_avoidCluster_empty_eq_cluster] at hbmem
    exact hbmem
  
  have hbT : b ∉ (↑T : Set (Site d)) := ray34_notMem_of_avoidCluster_nonempty hbinf.nonempty
  
  obtain ⟨r, hr0, hinj, hadj, hravoid⟩ :=
    ray34_konig (openSubgraph d ω) hbT hbinf
  refine ⟨b, hbconn, r, hr0, hinj, hadj, ?_⟩
  intro k
  have := hravoid k
  rwa [Finset.mem_coe] at this




theorem ray34_adj_removeSite_of_adj {ω : ConfigSpace (Sym2 (Site d))} {x a c : Site d}
    (hadj : (openSubgraph d ω).Adj a c) (ha : a ≠ x) (hc : c ≠ x) :
    (openSubgraph d (removeSite x ω)).Adj a c := by
  obtain ⟨hlat, hopen⟩ := hadj
  refine ⟨hlat, ?_⟩
  have hxnotin : x ∉ s(a, c) := by
    rw [Sym2.mem_iff]; push Not; exact ⟨fun h => ha h.symm, fun h => hc h.symm⟩
  rw [removeSite_apply_of_notMem hxnotin]; exact hopen











theorem ray34_removeSite_Tavoiding_ray_of_trif (ω : ConfigSpace (Sym2 (Site d))) {x : Site d}
    (hinf : (cluster d ω x).Infinite) (T : Finset (Site d)) :
    ∃ b : Site d, Connected d ω x b ∧
      ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧
        (∀ k, (openSubgraph d (removeSite x ω)).Adj (r k) (r (k + 1))) ∧
        (∀ k, r k ∉ T) := by
  classical
  set G := openSubgraph d ω with hG
  
  have hinf' : (ray34_AvoidCluster G ∅ x).Infinite := by
    rw [hG, ray34_avoidCluster_empty_eq_cluster]; exact hinf
  
  obtain ⟨b, hbmem, hbinf⟩ := ray34_infinite_avoidCluster_of_finset hinf' (insert x T)
  have hbconn : Connected d ω x b := by
    rw [hG, ray34_avoidCluster_empty_eq_cluster] at hbmem; exact hbmem
  have hbnot : b ∉ (↑(insert x T) : Set (Site d)) :=
    ray34_notMem_of_avoidCluster_nonempty hbinf.nonempty
  
  obtain ⟨r, hr0, hinj, hadj, hravoid⟩ := ray34_konig G hbnot hbinf
  
  have hrx : ∀ k, r k ≠ x := by
    intro k hk
    have := hravoid k
    rw [Finset.coe_insert, Set.mem_insert_iff] at this
    push Not at this
    exact this.1 hk
  have hrT : ∀ k, r k ∉ T := by
    intro k
    have := hravoid k
    rw [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at this
    push Not at this
    exact this.2
  refine ⟨b, hbconn, r, hr0, hinj, ?_, hrT⟩
  intro k
  exact ray34_adj_removeSite_of_adj (hadj k) (hrx k) (hrx (k + 1))
















def bc34_TavoidingCutArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) : Prop :=
  ∃ b : Site d → Site d,
    (∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (ray34_AvoidCluster (openSubgraph d (removeSite x ω))
        (↑(tfc_trifFinset ω n)) (b x)).Infinite) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      ¬ Connected d (removeSite y ω) (b y) (b x))









theorem bc34_TavoidingRayData_of_TavoidingCutArmData (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ) (h : bc34_TavoidingCutArmData ω n rank) :
    bc33_TavoidingRayData ω n rank := by
  classical
  obtain ⟨b, hbdata, hsplit⟩ := h
  refine ⟨b, ?_, hsplit⟩
  intro x hxbox htri
  obtain ⟨hbbox, hbconn, hbinf⟩ := hbdata x hxbox htri
  
  have hbT : b x ∉ (↑(tfc_trifFinset ω n) : Set (Site d)) :=
    ray34_notMem_of_avoidCluster_nonempty hbinf.nonempty
  
  obtain ⟨r, hr0, hinj, hadj, hravoid⟩ :=
    ray34_konig (openSubgraph d (removeSite x ω)) hbT hbinf
  refine ⟨hbbox, hbconn, r, hr0, hinj, hadj, ?_⟩
  intro k
  have := hravoid k
  rwa [Finset.mem_coe] at this















theorem ray34_avoidReach_removeSite_iff_connected_removeSites
    {ω : ConfigSpace (Sym2 (Site d))} {T : Finset (Site d)} {x b w : Site d}
    (hxT : x ∈ T) (hbT : b ∉ (↑T : Set (Site d))) :
    ray34_AvoidReach (openSubgraph d (removeSite x ω)) (↑T) b w ↔
      Connected d (removeSites T ω) b w := by
  classical
  constructor
  · 
    rintro ⟨p, hp⟩
    have hedges : ∀ e, e ∈ p.edges → e ∈ (openSubgraph d (removeSites T ω)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hu : u ∈ p.support := p.fst_mem_support_of_mem_edges he
        have hv : v ∈ p.support := p.snd_mem_support_of_mem_edges he
        have huT : u ∉ (↑T : Set (Site d)) := hp u hu
        have hvT : v ∉ (↑T : Set (Site d)) := hp v hv
        have hadj : (openSubgraph d (removeSite x ω)).Adj u v := p.adj_of_mem_edges he
        obtain ⟨hlat, _hopen⟩ := hadj
        
        have hnoT : ¬ ∃ t ∈ T, t ∈ s(u, v) := by
          rintro ⟨t, htT, hte⟩
          rw [Sym2.mem_iff] at hte
          rcases hte with rfl | rfl
          · exact huT (by rwa [Finset.mem_coe])
          · exact hvT (by rwa [Finset.mem_coe])
        have hxnotin : x ∉ s(u, v) := by
          rw [Sym2.mem_iff]; push Not
          exact ⟨fun h => huT (by rw [Finset.mem_coe]; exact h ▸ hxT),
                 fun h => hvT (by rw [Finset.mem_coe]; exact h ▸ hxT)⟩
        have hωopen : ω s(u, v) = true := by
          have := _hopen
          rwa [removeSite_apply_of_notMem hxnotin] at this
        rw [SimpleGraph.mem_edgeSet, openSubgraph_adj]
        refine ⟨hlat, ?_⟩
        rw [removeSites]; simp only [hnoT, if_false]; exact hωopen
    exact (p.transfer _ hedges).reachable
  · 
    rintro ⟨p⟩
    
    have hsuppT : ∀ u ∈ p.support, u ∉ (↑T : Set (Site d)) := by
      intro u hu huT
      rw [Finset.mem_coe] at huT
      
      rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges] at hu
      rcases hu with rfl | ⟨e, he, hue⟩
      · 
        by_cases hnil : p.Nil
        · have hbu : b = u := hnil.eq
          exact hbT (hbu ▸ Finset.mem_coe.mpr huT)
        · have hw : u ∈ p.support := p.end_mem_support
          rw [SimpleGraph.Walk.mem_support_iff_exists_mem_edges_of_not_nil hnil] at hw
          obtain ⟨e, he, hue⟩ := hw
          induction e using Sym2.ind with
          | _ a c =>
            have hadj : (openSubgraph d (removeSites T ω)).Adj a c := p.adj_of_mem_edges he
            obtain ⟨_hlat, hopen⟩ := hadj
            have hno : ¬ ∃ t ∈ T, t ∈ s(a, c) := by
              rw [removeSites] at hopen; by_contra hc; rw [if_pos hc] at hopen; exact Bool.noConfusion hopen
            exact hno ⟨u, huT, hue⟩
      · induction e using Sym2.ind with
        | _ a c =>
          have hadj : (openSubgraph d (removeSites T ω)).Adj a c := p.adj_of_mem_edges he
          obtain ⟨_hlat, hopen⟩ := hadj
          have hno : ¬ ∃ t ∈ T, t ∈ s(a, c) := by
            rw [removeSites] at hopen; by_contra hc; rw [if_pos hc] at hopen; exact Bool.noConfusion hopen
          exact hno ⟨u, huT, hue⟩
    have hedges : ∀ e, e ∈ p.edges → e ∈ (openSubgraph d (removeSite x ω)).edgeSet := by
      intro e he
      induction e using Sym2.ind with
      | _ u v =>
        have hadj : (openSubgraph d (removeSites T ω)).Adj u v := p.adj_of_mem_edges he
        obtain ⟨hlat, hopen⟩ := hadj
        have hnoT : ¬ ∃ t ∈ T, t ∈ s(u, v) := by
          rw [removeSites] at hopen; by_contra hc; rw [if_pos hc] at hopen; exact Bool.noConfusion hopen
        have hxnotin : x ∉ s(u, v) := fun hx => hnoT ⟨x, hxT, hx⟩
        have hωopen : ω s(u, v) = true := by
          rw [removeSites] at hopen; simpa only [hnoT, if_false] using hopen
        rw [SimpleGraph.mem_edgeSet, openSubgraph_adj]
        refine ⟨hlat, ?_⟩
        rw [removeSite_apply_of_notMem hxnotin]; exact hωopen
    exact ⟨p.transfer _ hedges, by rw [SimpleGraph.Walk.support_transfer]; exact hsuppT⟩



theorem ray34_avoidCluster_removeSite_eq_cluster_removeSites
    {ω : ConfigSpace (Sym2 (Site d))} {T : Finset (Site d)} {x b : Site d}
    (hxT : x ∈ T) (hbT : b ∉ (↑T : Set (Site d))) :
    ray34_AvoidCluster (openSubgraph d (removeSite x ω)) (↑T) b
      = cluster d (removeSites T ω) b := by
  ext w
  rw [ray34_mem_avoidCluster, mem_cluster,
    ray34_avoidReach_removeSite_iff_connected_removeSites hxT hbT]












theorem bc34_TavoidingRayData_of_globalCutArm (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (rank : Site d → ℕ ×ₗ ℕ)
    (b : Site d → Site d)
    (hbdata : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsplit : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      x ≠ y → Connected d ω x y → rank x < rank y →
      ¬ Connected d (removeSite y ω) (b y) (b x)) :
    bc33_TavoidingRayData ω n rank := by
  classical
  apply bc34_TavoidingRayData_of_TavoidingCutArmData ω n rank
  refine ⟨b, ?_, hsplit⟩
  intro x hxbox htri
  obtain ⟨hbbox, hbconn, hbinf⟩ := hbdata x hxbox htri
  refine ⟨hbbox, hbconn, ?_⟩
  
  have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
  have hbTf : b x ∉ tfc_trifFinset ω n :=
    stac_infiniteCluster_notMem (tfc_trifFinset ω n) ω hbinf
  have hbT : b x ∉ (↑(tfc_trifFinset ω n) : Set (Site d)) := by
    rw [Finset.mem_coe]; exact hbTf
  
  rw [ray34_avoidCluster_removeSite_eq_cluster_removeSites hxT hbT]
  exact hbinf
















theorem bc34_burton_keane_bernoulli_of_globalCutArm (hd : 1 ≤ d) (p : ℝ≥0)
    (hp1 : p ≤ 1) (hp0 : 0 < p)
    (rank : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → ℕ ×ₗ ℕ)
    (bfun : ConfigSpace (Sym2 (Site d)) → ℕ → Site d → Site d)
    (hinj : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ),
      ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank ω n x ≠ rank ω n y)
    (hbdata : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ x, x ∈ box d n → IsTrifurcation d ω x →
        bfun ω n x ∈ box d n ∧ Connected d ω x (bfun ω n x) ∧
        (cluster d (removeSites (tfc_trifFinset ω n) ω) (bfun ω n x)).Infinite)
    (hsplit : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank ω n x < rank ω n y →
        ¬ Connected d (removeSite y ω) (bfun ω n y) (bfun ω n x))
    (htrif : 0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω = ⊤} →
        0 < bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | IsTrifurcation d ω 0}) :
    (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
        {ω | numInfiniteClusters d ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1 (atLeastTwoInfinite d) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site d)) p hp1
          {ω | numInfiniteClusters d ω ≤ 1} = 1 :=
  bc33_burton_keane_bernoulli_of_TavoidingRayData hd p hp1 hp0 rank hinj
    (fun ω n hn => bc34_TavoidingRayData_of_globalCutArm ω n (rank ω n) (bfun ω n)
      (hbdata ω n hn) (hsplit ω n hn)) htrif
















theorem bc34_TavoidingRayData_of_threeChain_globalCut (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {x₀ m g : Site d} (b : Site d → Site d)
    (hx0box : x₀ ∈ box d n) (hmbox : m ∈ box d n) (hgbox : g ∈ box d n)
    (hx0m : x₀ ≠ m) (hx0g : x₀ ≠ g) (hmg : m ≠ g)
    (hthree : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = x₀ ∨ x = m ∨ x = g)
    (harm : ∀ x, x ∈ box d n → IsTrifurcation d ω x →
      b x ∈ box d n ∧ Connected d ω x (b x) ∧
      (cluster d (removeSites (tfc_trifFinset ω n) ω) (b x)).Infinite)
    (hsxm : ¬ Connected d (removeSite m ω) (b m) (b x₀))
    (hsxg : ¬ Connected d (removeSite g ω) (b g) (b x₀))
    (hsmg : ¬ Connected d (removeSite g ω) (b g) (b m)) :
    bc33_TavoidingRayData ω n
      (fun z => if z = x₀ then toLex (0, 0)
                else if z = m then toLex (1, 0) else toLex (2, 0)) := by
  classical
  set dep : Site d → ℕ := fun z => if z = x₀ then 0 else if z = m then 1 else 2 with hdep
  have hdepx0 : dep x₀ = 0 := by simp [hdep]
  have hdepm : dep m = 1 := by simp [hdep, hx0m.symm]
  have hdepg : dep g = 2 := by simp [hdep, hx0g.symm, hmg.symm]
  have hrankeq : (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) := by
    funext z; simp only [hdep]; split_ifs <;> rfl
  rw [show (fun z : Site d => if z = x₀ then toLex (0, 0)
        else if z = m then toLex (1, 0) else toLex (2, 0))
      = fun z => toLex (dep z, 0) from hrankeq]
  apply bc34_TavoidingRayData_of_globalCutArm ω n _ b harm
  intro x hxbox htri y hybox htriy hxy _ hlt
  rcases hthree x hxbox htri with rfl | rfl | rfl <;>
    rcases hthree y hybox htriy with rfl | rfl | rfl
  · exact absurd rfl hxy
  · exact hsxm
  · exact hsxg
  · rw [hdepm, hdepx0] at hlt
    exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
  · exact absurd rfl hxy
  · exact hsmg
  · rw [hdepg, hdepx0] at hlt
    exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
  · rw [hdepg, hdepm] at hlt
    exact absurd hlt (stt_lex_not_lt_fst (by norm_num))
  · exact absurd rfl hxy

end StatMech.Walls
