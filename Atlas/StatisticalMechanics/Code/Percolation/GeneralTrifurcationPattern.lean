/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






import Code.Percolation.InfiniteClusterTail
import Code.Percolation.LatticeThreeExitTree
import Code.Percolation.TreeExteriorAmalgam
import Code.Percolation.CanonicalTrifCount
import Code.Percolation.OutwardArmForestClose
import Code.FK.FinitePatternEnergy
import Code.IsingFK.HisingBoxClose
import Code.Lattice.ContourCountInjection

open Set SimpleGraph Finset
open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech.Percolation

variable {d : ℕ}


noncomputable def programmedTreeEdges {W : Type*} [Fintype W]
    (T : SimpleGraph W) [DecidableRel T.Adj] (f : W → Site d) :
    Finset (Sym2 (Site d)) := T.edgeFinset.image (Sym2.map f)


noncomputable def programmedTreePattern (I O : Finset (Sym2 (Site d))) :
    ConfigSpace ↥I := fun e => decide (e.1 ∈ O)


def exteriorOpenGraph (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    SimpleGraph (Site d) where
  Adj x y := (openSubgraph d omega).Adj x y ∧ x ∉ box d n ∧ y ∉ box d n
  symm := by rintro x y ⟨h, hx, hy⟩; exact ⟨h.symm, hy, hx⟩
  loopless := ⟨fun _ h => (openSubgraph d omega).irrefl h.1⟩

theorem exteriorOpenGraph_le (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    exteriorOpenGraph omega n ≤ openSubgraph d omega := fun _ _ h => h.1




theorem three_infinite_clusters_finite_pattern_canonical_trifurcation
    (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Fin 3 → Site d)
    (hx : ∀ i, x i ∈ box d n)
    (hinf : ∀ i, (cluster d omega (x i)).Infinite)
    (hclusters : ∀ i j, i ≠ j →
      cluster d omega (x i) ≠ cluster d omega (x j)) :
    ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n)) (hub : Site d),
      IsCanonicalTrifurcation d
        (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta omega) hub := by
  classical
  let K := boxFinsetBK d n
  have hxK : ∀ i, x i ∈ K := fun i => by
    simpa only [K, boxFinsetBK, Set.Finite.mem_toFinset] using hx i
  let D : (i : Fin 3) → InfiniteClusterTailData omega K (x i) := fun i =>
    infiniteClusterTailData omega (x i) (hinf i) K (hxK i)
  let inside : Fin 3 → Site d := fun i => (D i).inside
  let outside : Fin 3 → Site d := fun i => (D i).outside
  have hinside : ∀ i, inside i ∈ box d n := fun i => by
    simpa only [inside, K, boxFinsetBK, Set.Finite.mem_toFinset] using (D i).inside_mem
  have hout : ∀ i, outside i ∉ box d n := fun i h =>
    (D i).outside_not_mem (by
      simpa only [K, boxFinsetBK, Set.Finite.mem_toFinset] using h)
  have houtinj : Function.Injective outside := by
    intro i j hij
    by_contra hne
    have hi : outside i ∈ cluster d omega (x i) :=
      (D i).tail_subset_cluster (D i).outside_mem_tail
    have hj : outside j ∈ cluster d omega (x j) :=
      (D j).tail_subset_cluster (D j).outside_mem_tail
    rw [hij] at hi
    exact hclusters i j hne
      ((cluster_eq_of_connected hi).trans (cluster_eq_of_connected hj).symm)
  have hexit : ∀ i, (hypercubicLattice d).Adj (inside i) (outside i) :=
    fun i => (D i).exit_open.1
  obtain ⟨C, T, hTdec, hub, stem, leaf, hTree, hembedInj, hTG, hTlat,
      hstemInj, hstemAdj, hleafInj, hleafSite, htipSurj, hstemLeaf,
      hTreach, hTcut⟩ :=
    lattice_three_exit_tree inside outside hinside hout houtinj hexit
  let embed : C → Site d := fun z => threeExitSite outside z.1
  have hembed : Function.Injective embed := hembedInj
  choose sigma hsigma using hleafSite
  have hsigma_inj : Function.Injective sigma := by
    intro i j hij
    apply hleafInj
    apply hembed
    change threeExitSite outside (leaf i).1 = threeExitSite outside (leaf j).1
    rw [hsigma i, hsigma j, hij]
  let I := StatMech.Ising.bondFinsetTouch d n
  let O := programmedTreeEdges T embed
  let eta := programmedTreePattern I O
  let omega' := StatMech.FK.setPattern I eta omega
  let E := exteriorOpenGraph omega n
  let U := openSubgraph d omega'
  have htreeTouch : ∀ {a b : C}, T.Adj a b → s(embed a, embed b) ∈ I := by
    intro a b hab
    apply StatMech.Lattice.mk_mem_bondFinsetTouch (hTlat a b hab)
    have h := hTG a b hab
    rcases ha : a.1 with qa | ia <;> rcases hb : b.1 with qb | ib
    · exact Or.inl (by simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using qa.2)
    · exact Or.inl (by simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using qa.2)
    · exact Or.inr (by simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using qb.2)
    · simp [threeExitGraph, ha, hb] at h
  have htreeOpen : ∀ {a b : C}, T.Adj a b → U.Adj (embed a) (embed b) := by
    intro a b hab
    dsimp only [U, omega']
    rw [openSubgraph_adj]
    refine ⟨hTlat a b hab, ?_⟩
    have hI := htreeTouch hab
    rw [StatMech.FK.setPattern_of_mem eta hI]
    simp only [eta, programmedTreePattern, decide_eq_true_eq]
    unfold O programmedTreeEdges
    rw [Finset.mem_image]
    exact ⟨s(a, b), by simpa using hab, by simp⟩
  let treeHom : T →g U := {
    toFun := embed
    map_rel' := fun {_ _} h => htreeOpen h
  }
  have hE_le_U : E ≤ U := by
    intro a b hab
    have hnotI : s(a, b) ∉ I := by
      change s(a, b) ∉ StatMech.Ising.bondFinsetTouch d n
      rw [StatMech.IsingFK.hbx_mem_bondFinsetTouch_iff]
      push Not
      intro _
      exact ⟨hab.2.1, hab.2.2⟩
    change (openSubgraph d (StatMech.FK.setPattern I eta omega)).Adj a b
    rw [openSubgraph_adj]
    refine ⟨hab.1.1, ?_⟩
    rw [StatMech.FK.setPattern_of_not_mem eta hnotI]
    exact hab.1.2
  have hEsep : ∀ i j, i ≠ j →
      ¬ E.Reachable (embed (leaf i)) (embed (leaf j)) := by
    intro i j hij hr
    have hr' := hr.mono (exteriorOpenGraph_le omega n)
    change (openSubgraph d omega).Reachable
      (threeExitSite outside (leaf i).1)
      (threeExitSite outside (leaf j).1) at hr'
    rw [hsigma i, hsigma j] at hr'
    have hi : Connected d omega (x (sigma i)) (outside (sigma i)) :=
      (D (sigma i)).tail_subset_cluster (D (sigma i)).outside_mem_tail
    have hj : Connected d omega (x (sigma j)) (outside (sigma j)) :=
      (D (sigma j)).tail_subset_cluster (D (sigma j)).outside_mem_tail
    have hconn : Connected d omega (x (sigma i)) (x (sigma j)) :=
      hi.trans (hr'.trans hj.symm)
    exact hclusters (sigma i) (sigma j) (fun h => hij (hsigma_inj h))
      (cluster_eq_of_connected hconn)
  have hEonly : ∀ z y, E.Adj (embed z) y → ∃ i, z = leaf i := by
    intro z y hzy
    rcases hz : z.1 with q | k
    · exfalso
      have hqbox : q.1 ∈ box d n := by
        simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using q.2
      have hzsite : embed z = q.1 := by simp [embed, threeExitSite, hz]
      exact hzy.2.1 (hzsite.symm ▸ hqbox)
    · obtain ⟨i, hi⟩ := htipSurj k
      exact ⟨i, Subtype.ext (hz.trans hi.symm)⟩
  have hhubCore : ∃ q : ↑(boxFinsetBK d n), hub.1 = Sum.inl q := by
    rcases hh : hub.1 with q | j
    · exact ⟨q, rfl⟩
    · exfalso
      have hdeg := threeExitTip_degree_one inside hinside j
      rw [degree_eq_one_iff_existsUnique_adj] at hdeg
      obtain ⟨z, _hz, huniq⟩ := hdeg
      have h0 : (stem 0).1 = z := huniq (stem 0).1 (by
        simpa only [hh] using hTG hub (stem 0) (hstemAdj 0))
      have h1 : (stem 1).1 = z := huniq (stem 1).1 (by
        simpa only [hh] using hTG hub (stem 1) (hstemAdj 1))
      exact (by decide : (0 : Fin 3) ≠ 1)
        (hstemInj (Subtype.ext (h0.trans h1.symm)))
  obtain ⟨hubCore, hhubCore⟩ := hhubCore
  have hhubBox : embed hub ∈ box d n := by
    have hmem : hubCore.1 ∈ box d n := by
      simpa only [boxFinsetBK, Set.Finite.mem_toFinset] using hubCore.2
    simpa only [embed, threeExitSite, hhubCore] using hmem
  have hUdecomp : ∀ {a b}, U.Adj a b →
      E.Adj a b ∨ ∃ u v, T.Adj u v ∧ embed u = a ∧ embed v = b := by
    intro a b hab
    dsimp only [U, omega'] at hab
    rw [openSubgraph_adj] at hab
    by_cases htouch : a ∈ box d n ∨ b ∈ box d n
    · right
      have hI : s(a, b) ∈ I :=
        StatMech.Lattice.mk_mem_bondFinsetTouch hab.1 htouch
      have hopen := hab.2
      rw [StatMech.FK.setPattern_of_mem eta hI] at hopen
      have hO : s(a, b) ∈ O := by
        simpa only [eta, programmedTreePattern, decide_eq_true_eq] using hopen
      unfold O programmedTreeEdges at hO
      rw [Finset.mem_image] at hO
      obtain ⟨e, he, heq⟩ := hO
      induction e with
      | h u v =>
          rw [SimpleGraph.mem_edgeFinset] at he
          simp only [Sym2.map_mk, Sym2.eq_iff] at heq
          rcases heq with ⟨hu, hv⟩ | ⟨hu, hv⟩
          · exact ⟨u, v, he, hu, hv⟩
          · exact ⟨v, u, he.symm, hv, hu⟩
    · left
      push Not at htouch
      have hnotI : s(a, b) ∉ I := by
        change s(a, b) ∉ StatMech.Ising.bondFinsetTouch d n
        rw [StatMech.IsingFK.hbx_mem_bondFinsetTouch_iff]
        push Not
        intro _
        exact ⟨htouch.1, htouch.2⟩
      have hopen := hab.2
      rw [StatMech.FK.setPattern_of_not_mem eta hnotI] at hopen
      change E.Adj a b
      exact ⟨⟨hab.1, hopen⟩, htouch.1, htouch.2⟩
  have hUsep := tree_exterior_amalgam_separated T E U embed hembed hub leaf
    hTcut hEsep hEonly hUdecomp
  have hE_le_Ucut : E ≤ U.deleteIncidenceSet (embed hub) := by
    intro a b hab
    rw [deleteIncidenceSet_adj]
    refine ⟨hE_le_U hab, ?_, ?_⟩
    · intro ha
      exact hab.2.1 (ha ▸ hhubBox)
    · intro hb
      exact hab.2.2 (hb ▸ hhubBox)
  let treeCutHom : T.deleteIncidenceSet hub →g
      U.deleteIncidenceSet (embed hub) := {
    toFun := embed
    map_rel' := by
      intro a b hab
      rw [deleteIncidenceSet_adj] at hab ⊢
      refine ⟨htreeOpen hab.1, ?_, ?_⟩
      · intro ha
        exact hab.2.1 (hembed ha)
      · intro hb
        exact hab.2.2 (hembed hb)
  }
  have hstemLeafCut : ∀ i,
      (U.deleteIncidenceSet (embed hub)).Reachable
        (embed (stem i)) (embed (leaf i)) := fun i =>
    by simpa [treeCutHom] using (hstemLeaf i).map treeCutHom
  have htailE : ∀ i, ∀ z ∈ (D (sigma i)).tail,
      E.Reachable (embed (leaf i)) z := by
    intro i z hz
    have houtTail := (D (sigma i)).outside_mem_tail
    obtain ⟨ha, hb, hr⟩ :=
      (D (sigma i)).tail_connected_outside
        (outside (sigma i)) houtTail z hz
    let f : ((openSubgraph d omega).induce (K : Set (Site d))ᶜ) →g E := {
      toFun := fun q => q.1
      map_rel' := by
        intro a b hab
        refine ⟨hab, ?_, ?_⟩
        · intro ha
          apply a.2
          change a.1 ∈ K
          simpa only [K, boxFinsetBK, Set.Finite.mem_toFinset] using ha
        · intro hb
          apply b.2
          change b.1 ∈ K
          simpa only [K, boxFinsetBK, Set.Finite.mem_toFinset] using hb
    }
    change E.Reachable (threeExitSite outside (leaf i).1) z
    rw [hsigma i]
    exact hr.map f
  have hremove : openSubgraph d (removeSite (embed hub) omega') =
      U.deleteIncidenceSet (embed hub) := by
    rw [oaf_openSubgraph_removeSite]
    ext a b
    simp only [oaf_cutGraph, deleteIncidenceSet_adj, U]
  have hstemInf : ∀ i,
      (cluster d (removeSite (embed hub) omega') (embed (stem i))).Infinite := by
    intro i
    apply (D (sigma i)).tail_infinite.mono
    intro z hz
    change (openSubgraph d (removeSite (embed hub) omega')).Reachable
      (embed (stem i)) z
    rw [hremove]
    exact (hstemLeafCut i).trans ((htailE i z hz).mono hE_le_Ucut)
  have hstemSep : ∀ i j, i ≠ j →
      ¬ (U.deleteIncidenceSet (embed hub)).Reachable
        (embed (stem i)) (embed (stem j)) := by
    intro i j hij hr
    exact hUsep i j hij
      ((hstemLeafCut i).symm.trans (hr.trans (hstemLeafCut j)))
  refine ⟨eta, embed hub, embed (stem 0), embed (stem 1), embed (stem 2),
    ?_, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_⟩
    · intro h
      exact (by decide : (0 : Fin 3) ≠ 1) (hstemInj (hembed h))
    · intro h
      exact (by decide : (0 : Fin 3) ≠ 2) (hstemInj (hembed h))
    · intro h
      exact (by decide : (1 : Fin 3) ≠ 2) (hstemInj (hembed h))
  · exact ⟨htreeOpen (hstemAdj 0), htreeOpen (hstemAdj 1),
      htreeOpen (hstemAdj 2)⟩
  · exact ⟨hstemInf 0, hstemInf 1, hstemInf 2⟩
  · change
      (¬ (openSubgraph d (removeSite (embed hub) omega')).Reachable
        (embed (stem 0)) (embed (stem 1))) ∧
      (¬ (openSubgraph d (removeSite (embed hub) omega')).Reachable
        (embed (stem 0)) (embed (stem 2))) ∧
      (¬ (openSubgraph d (removeSite (embed hub) omega')).Reachable
        (embed (stem 1)) (embed (stem 2)))
    rw [hremove]
    exact ⟨hstemSep 0 1 (by decide), hstemSep 0 2 (by decide),
      hstemSep 1 2 (by decide)⟩


theorem three_infinite_clusters_finite_pattern_trifurcation
    (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x : Fin 3 → Site d)
    (hx : ∀ i, x i ∈ box d n)
    (hinf : ∀ i, (cluster d omega (x i)).Infinite)
    (hclusters : ∀ i j, i ≠ j →
      cluster d omega (x i) ≠ cluster d omega (x j)) :
    ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n)) (hub : Site d),
      IsTrifurcation d
        (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta omega) hub := by
  obtain ⟨eta, hub, h⟩ :=
    three_infinite_clusters_finite_pattern_canonical_trifurcation
      omega n x hx hinf hclusters
  exact ⟨eta, hub, ctc2_isTrifurcation_of_canonical h⟩


theorem three_sites_finite_pattern_canonical_trifurcation
    (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) (a b c : Site d)
    (ha : a ∈ box d n) (hb : b ∈ box d n) (hc : c ∈ box d n)
    (hia : (cluster d omega a).Infinite)
    (hib : (cluster d omega b).Infinite)
    (hic : (cluster d omega c).Infinite)
    (hab : cluster d omega a ≠ cluster d omega b)
    (hac : cluster d omega a ≠ cluster d omega c)
    (hbc : cluster d omega b ≠ cluster d omega c) :
    ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n)) (hub : Site d),
      IsCanonicalTrifurcation d
        (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta omega) hub := by
  let x : Fin 3 → Site d := ![a, b, c]
  apply three_infinite_clusters_finite_pattern_canonical_trifurcation omega n x
  · intro i
    fin_cases i <;> assumption
  · intro i
    fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [x, ne_comm]


theorem three_sites_finite_pattern_trifurcation
    (omega : ConfigSpace (Sym2 (Site d))) (n : ℕ) (a b c : Site d)
    (ha : a ∈ box d n) (hb : b ∈ box d n) (hc : c ∈ box d n)
    (hia : (cluster d omega a).Infinite)
    (hib : (cluster d omega b).Infinite)
    (hic : (cluster d omega c).Infinite)
    (hab : cluster d omega a ≠ cluster d omega b)
    (hac : cluster d omega a ≠ cluster d omega c)
    (hbc : cluster d omega b ≠ cluster d omega c) :
    ∃ (eta : ConfigSpace ↥(StatMech.Ising.bondFinsetTouch d n)) (hub : Site d),
      IsTrifurcation d
        (StatMech.FK.setPattern (StatMech.Ising.bondFinsetTouch d n) eta omega) hub := by
  let x : Fin 3 → Site d := ![a, b, c]
  apply three_infinite_clusters_finite_pattern_trifurcation omega n x
  · intro i
    fin_cases i <;> assumption
  · intro i
    fin_cases i <;> assumption
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [x, ne_comm]

end StatMech.Percolation
