/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/









import Code.Walls.binsinsertion

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace
open StatMech.Percolation
open StatMech.Ising StatMech.IsingFK

namespace StatMech.Walls

set_option linter.style.longLine false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 20000




theorem bins_connected_of_walk_edges_open {x y : Site 2}
    (P : (hypercubicLattice 2).Walk x y) (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : forall e, e ∈ P.edges -> omega e = true) : Connected 2 omega x y := by
  induction P with
  | nil => exact ⟨Walk.nil⟩
  | @cons x y z hxy P ih =>
      apply (IsOpenEdge.connected (ω := omega) (x := x) (y := y) ?_).trans
        (ih (fun e he => hopen e (by simp [he])))
      exact ⟨hxy, hopen s(x, y) (by simp)⟩


theorem bins_cylinder_value {I : Finset (Sym2 (Site 2))}
    {eta : ConfigSpace (Subtype fun e => e ∈ I)} {omega : ConfigSpace (Sym2 (Site 2))}
    (hcyl : omega ∈ cylinder I ({eta} : Set (ConfigSpace (Subtype fun e => e ∈ I))))
    (e : Sym2 (Site 2)) (he : e ∈ I) : omega e = eta ⟨e, he⟩ := by
  rw [MeasureTheory.mem_cylinder, Set.mem_singleton_iff] at hcyl
  exact congrFun hcyl ⟨e, he⟩





theorem bins_corridors_of_same_side (n : ℕ) (hn : 1 ≤ n)
    (v1 v2 v3 : Site 2) (hv1 : v1 ∈ box 2 n) (hv2 : v2 ∈ box 2 n)
    (hv3 : v3 ∈ box 2 n) (h12 : v1 ≠ v2) (h13 : v1 ≠ v3) (h23 : v2 ≠ v3)
    (hside :
      (v1 0 = (n : ℤ) ∧ v2 0 = (n : ℤ) ∧ v3 0 = (n : ℤ)) ∨
      (v1 0 = -(n : ℤ) ∧ v2 0 = -(n : ℤ) ∧ v3 0 = -(n : ℤ)) ∨
      (v1 1 = (n : ℤ) ∧ v2 1 = (n : ℤ) ∧ v3 1 = (n : ℤ)) ∨
      (v1 1 = -(n : ℤ) ∧ v2 1 = -(n : ℤ) ∧ v3 1 = -(n : ℤ))) :
    bcor_Corridors n v1 v2 v3 := by
  rw [mem_box] at hv1 hv2 hv3
  rcases hside with hr | hl | ht | hb
  · have h := bcor_corridors_same_right_of_distinct n hn (v1 1) (v2 1) (v3 1)
      (hv1 1) (hv2 1) (hv3 1)
      (fun h => h12 (by ext q; fin_cases q <;> simp_all))
      (fun h => h13 (by ext q; fin_cases q <;> simp_all))
      (fun h => h23 (by ext q; fin_cases q <;> simp_all))
    convert h using 1 <;> ext q <;> fin_cases q <;> simp_all
  · have h := bcor_corridors_same_right_of_distinct n hn (-v1 1) (-v2 1) (-v3 1)
      (by simpa using hv1 1) (by simpa using hv2 1) (by simpa using hv3 1)
      (by intro h; apply h12; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h13; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h23; ext q <;> fin_cases q <;> simp_all)
    have hh := bcor_corridors_rot90_iterate 2 h
    convert hh using 1 <;> ext q <;> fin_cases q <;>
      simp [Function.iterate_succ_apply', rot90Fun_apply] <;> omega
  · have h := bcor_corridors_same_right_of_distinct n hn (-v1 0) (-v2 0) (-v3 0)
      (by simpa using hv1 0) (by simpa using hv2 0) (by simpa using hv3 0)
      (by intro h; apply h12; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h13; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h23; ext q <;> fin_cases q <;> simp_all)
    have hh := bcor_corridors_rot90 h
    convert hh using 1 <;> ext q <;> fin_cases q <;> simp [rot90Fun_apply] <;> omega
  · have h := bcor_corridors_same_right_of_distinct n hn (v1 0) (v2 0) (v3 0)
      (hv1 0) (hv2 0) (hv3 0)
      (by intro h; apply h12; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h13; ext q <;> fin_cases q <;> simp_all)
      (by intro h; apply h23; ext q <;> fin_cases q <;> simp_all)
    have hh := bcor_corridors_rot90_iterate 3 h
    convert hh using 1 <;> ext q <;> fin_cases q <;>
      simp [Function.iterate_succ_apply', rot90Fun_apply] <;> omega




structure bins_Branch where
  v : Site 2
  u : Site 2
  P : (hypercubicLattice 2).Walk ![0, 0] v


def bins_branchEdges (B : Fin 3 → bins_Branch) : Finset (Sym2 (Site 2)) :=
  (Finset.univ.biUnion fun i => (B i).P.edges.toFinset) ∪
    Finset.univ.image (fun i => s((B i).v, (B i).u))



def bins_branchSide (rho : ConfigSpace (Sym2 (Site 2))) (B : bins_Branch) : Set (Site 2) :=
  ({z | z ∈ B.P.support ∧ z ≠ ![0, 0]} : Set (Site 2)) ∪ cluster 2 rho B.u


theorem bins_walk_edge_mem_touch {n : ℕ} {x y : Site 2}
    (P : (hypercubicLattice 2).Walk x y)
    (hbox : ∀ z ∈ P.support, z ∈ box 2 n) :
    P.edges.toFinset ⊆ bondFinsetTouch 2 n := by
  intro e he
  rw [List.mem_toFinset] at he
  induction P with
  | nil => simp at he
  | @cons x y z hxy P ih =>
      rw [Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · rw [hbx_mem_bondFinsetTouch_iff]
        exact ⟨hxy, Or.inl (hbox x (by simp))⟩
      · apply ih
        intro w hw
        exact hbox w (by simp [hw])
        exact he


theorem bins_extCluster_avoids_box (n : ℕ) (omega : ConfigSpace (Sym2 (Site 2)))
    (u : Site 2) (hu : u ∉ box 2 n) :
    Disjoint (cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) u)
      (box 2 n) := by
  rw [Set.disjoint_left]
  intro z hz hzbox
  rw [bins_cluster_closeTouch_eq_removeBox] at hz
  have hconn : Connected 2 (removeSites (boxFinset 2 n) omega) u z := mem_cluster.mp hz
  have humem : u ∈ cluster 2 (removeSites (boxFinset 2 n) omega) z :=
    mem_cluster.mpr hconn.symm
  have hzfin : z ∈ boxFinset 2 n := by
    rw [mem_boxFinset]
    exact hzbox
  rw [stac_removeSites_cluster_singleton (boxFinset 2 n) omega hzfin] at humem
  have huz : u = z := by simpa using humem
  exact hu (huz ▸ hzbox)


def bins_touchPattern (n : ℕ) (B : Fin 3 → bins_Branch) :
    ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n) :=
  fun e => decide (e.1 ∈ bins_branchEdges B)



theorem bins_touchPattern_value {n : ℕ} {B : Fin 3 → bins_Branch}
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hcyl : omega ∈ cylinder (bondFinsetTouch 2 n)
      ({bins_touchPattern n B} : Set
        (ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n))))
    {e : Sym2 (Site 2)} (he : e ∈ bondFinsetTouch 2 n) :
    omega e = true ↔ e ∈ bins_branchEdges B := by
  rw [bins_cylinder_value hcyl e he, bins_touchPattern]
  simp



theorem bins_tail_connected_remove_start {x v : Site 2}
    (P : (hypercubicLattice 2).Walk x v) (hp : P.IsPath) (hv : v ≠ x)
    (omega : ConfigSpace (Sym2 (Site 2)))
    (hopen : ∀ e ∈ P.edges, omega e = true) :
    Connected 2 (removeSite x omega) P.snd v := by
  cases P with
  | nil => exact absurd rfl hv
  | @cons x y v hxy Q =>
      have hconn : Connected 2 (removeSite x omega) y v :=
        bins_connected_of_walk_edges_open Q (removeSite x omega) (by
          intro e he
          have hex : x ∉ e := by
            intro hxe
            have hxs : x ∈ Q.support := Q.mem_support_of_mem_edges he hxe
            have hnodup := hp.support_nodup
            rw [Walk.support_cons, List.nodup_cons] at hnodup
            exact hnodup.1 hxs
          unfold removeSite
          rw [if_neg hex]
          exact hopen e (by simp [he]))
      simpa using hconn



theorem bins_branch_connected {n : ℕ} {B : Fin 3 → bins_Branch}
    (i : Fin 3) (hp : (B i).P.IsPath) (hv : (B i).v ≠ ![0, 0])
    (hadj : (hypercubicLattice 2).Adj (B i).v (B i).u)
    (hu : (B i).u ≠ ![0, 0])
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hcyl : omega ∈ cylinder (bondFinsetTouch 2 n)
      ({bins_touchPattern n B} : Set
        (ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n))))
    (hbox : ∀ z ∈ (B i).P.support, z ∈ box 2 n) :
    Connected 2 (removeSite 0 omega) (B i).P.snd (B i).u := by
  have hedge (e : Sym2 (Site 2)) (he : e ∈ (B i).P.edges) : omega e = true := by
    have heI := bins_walk_edge_mem_touch (B i).P hbox (List.mem_toFinset.mpr he)
    apply (bins_touchPattern_value hcyl heI).2
    rw [bins_branchEdges, Finset.mem_union]
    left
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, List.mem_toFinset.mpr he⟩
  have htail' := bins_tail_connected_remove_start (B i).P hp hv omega hedge
  have htail : Connected 2 (removeSite 0 omega) (B i).P.snd (B i).v := by
    simpa [bcor_origin_eq] using htail'
  have hattI : s((B i).v, (B i).u) ∈ bondFinsetTouch 2 n := by
    rw [hbx_mem_bondFinsetTouch_iff]
    exact ⟨hadj, Or.inl (hbox (B i).v (by simp))⟩
  have hattOpen : omega s((B i).v, (B i).u) = true := by
    apply (bins_touchPattern_value hcyl hattI).2
    rw [bins_branchEdges, Finset.mem_union]
    right
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hatt : IsOpenEdge 2 (removeSite 0 omega) (B i).v (B i).u := by
    refine ⟨hadj, ?_⟩
    unfold removeSite
    have h0 : (0 : Site 2) ∉ s((B i).v, (B i).u) := by
      simp only [Sym2.mem_iff, not_or]
      constructor
      · intro h; apply hv; simpa [bcor_origin_eq] using h.symm
      · intro h; apply hu; simpa [bcor_origin_eq] using h.symm
    rw [if_neg h0]
    exact hattOpen
  exact htail.trans hatt.connected



theorem bins_branchSide_openClosed {n : ℕ} {B : Fin 3 → bins_Branch}
    (hbox : ∀ i z, z ∈ (B i).P.support → z ∈ box 2 n)
    (hpathDisj : ∀ i j, i ≠ j → ∀ z,
      z ∈ (B i).P.support → z ∈ (B j).P.support → z = ![0, 0])
    (hadj : ∀ i, (hypercubicLattice 2).Adj (B i).v (B i).u)
    (huout : ∀ i, (B i).u ∉ box 2 n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hcyl : omega ∈ cylinder (bondFinsetTouch 2 n)
      ({bins_touchPattern n B} : Set
        (ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n))))
    (hclusterNe : ∀ i j, i ≠ j →
      cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i).u ≠
      cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B j).u)
    (i : Fin 3) :
    ∀ z w : Site 2, z ∈ bins_branchSide
        (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i) →
      IsOpenEdge 2 (removeSite 0 omega) z w →
      w ∈ bins_branchSide
        (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i) := by
  let rho := removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)
  intro z w hz hopen
  have hz0 : z ≠ ![0, 0] := by
    intro h
    subst z
    have hmem : (0 : Site 2) ∈ s((![0, 0] : Site 2), w) := by
      rw [bcor_origin_eq]
      simp
    exact (by simpa [IsOpenEdge, removeSite, hmem] using hopen)
  have hw0 : w ≠ ![0, 0] := by
    intro h
    subst w
    have hmem : (0 : Site 2) ∈ s(z, (![0, 0] : Site 2)) := by
      rw [bcor_origin_eq]
      simp
    exact (by simpa [IsOpenEdge, removeSite, hmem] using hopen)
  have hnot0 : (0 : Site 2) ∉ s(z, w) := by
    simp only [Sym2.mem_iff, not_or]
    constructor
    · intro h; apply hz0; simpa [bcor_origin_eq] using h.symm
    · intro h; apply hw0; simpa [bcor_origin_eq] using h.symm
  have hopenOmega : omega s(z, w) = true := by
    have hval := hopen.2
    unfold removeSite at hval
    rw [if_neg hnot0] at hval
    exact hval
  have hclusterDisj {a b : Fin 3} (hab : a ≠ b) :
      Disjoint (cluster 2 rho (B a).u) (cluster 2 rho (B b).u) := by
    rw [Set.disjoint_left]
    intro q hqa hqb
    apply hclusterNe a b hab
    exact cluster_eq_of_connected ((mem_cluster.mp hqa).trans (mem_cluster.mp hqb).symm)
  have zpath_of_box (hzbox : z ∈ box 2 n) : z ∈ (B i).P.support := by
    rcases hz with hzpath | hzcluster
    · exact hzpath.1
    · exact absurd hzbox
        (Set.disjoint_left.mp (bins_extCluster_avoids_box n omega (B i).u (huout i))
          hzcluster)
  have zw_branch_of_touch (htouch : s(z, w) ∈ bondFinsetTouch 2 n) :
      s(z, w) ∈ bins_branchEdges B :=
    (bins_touchPattern_value hcyl htouch).1 hopenOmega
  by_cases hzbox : z ∈ box 2 n
  · have htouch : s(z, w) ∈ bondFinsetTouch 2 n := by
      rw [hbx_mem_bondFinsetTouch_iff]
      exact ⟨hopen.1, Or.inl hzbox⟩
    have hG := zw_branch_of_touch htouch
    rw [bins_branchEdges, Finset.mem_union] at hG
    rcases hG with hwalk | hatt
    · rw [Finset.mem_biUnion] at hwalk
      obtain ⟨j, _, hjedge⟩ := hwalk
      rw [List.mem_toFinset] at hjedge
      have hzj := (B j).P.fst_mem_support_of_mem_edges hjedge
      have hwj := (B j).P.snd_mem_support_of_mem_edges hjedge
      have hij : i = j := by
        by_contra hij
        exact hz0 (hpathDisj i j hij z (zpath_of_box hzbox) hzj)
      subst j
      exact Or.inl ⟨hwj, hw0⟩
    · rw [Finset.mem_image] at hatt
      obtain ⟨j, _, heq⟩ := hatt
      rw [Sym2.eq_iff] at heq
      rcases heq with ⟨hzv, hwu⟩ | ⟨hzu, hwv⟩
      · have hzj : z ∈ (B j).P.support := by simpa [hzv] using (B j).P.getVert_mem_support (B j).P.length
        have hij : i = j := by
          by_contra hij
          exact hz0 (hpathDisj i j hij z (zpath_of_box hzbox) hzj)
        subst j
        exact Or.inr (hwu ▸ self_mem_cluster rho (B i).u)
      · exact absurd (hwv ▸ hzbox) (huout j)
  · have hzcluster : z ∈ cluster 2 rho (B i).u := by
      rcases hz with hzpath | hzcluster
      · exact absurd (hbox i z hzpath.1) hzbox
      · exact hzcluster
    by_cases hwbox : w ∈ box 2 n
    · have htouch : s(z, w) ∈ bondFinsetTouch 2 n := by
        rw [hbx_mem_bondFinsetTouch_iff]
        exact ⟨hopen.1, Or.inr hwbox⟩
      have hG := zw_branch_of_touch htouch
      rw [bins_branchEdges, Finset.mem_union] at hG
      rcases hG with hwalk | hatt
      · rw [Finset.mem_biUnion] at hwalk
        obtain ⟨j, _, hjedge⟩ := hwalk
        rw [List.mem_toFinset] at hjedge
        exact absurd (hbox j z ((B j).P.fst_mem_support_of_mem_edges hjedge)) hzbox
      · rw [Finset.mem_image] at hatt
        obtain ⟨j, _, heq⟩ := hatt
        rw [Sym2.eq_iff] at heq
        rcases heq with ⟨hzv, hwu⟩ | ⟨hzu, hwv⟩
        · exact absurd (hzv ▸ hbox j (B j).v (by simp)) hzbox
        · have hij : i = j := by
            by_contra hij
            exact (Set.disjoint_left.mp (hclusterDisj hij)) hzcluster
              (hwv ▸ self_mem_cluster rho (B j).u)
          subst j
          exact Or.inl ⟨by rw [← hzu]; simp, hw0⟩
    · apply Or.inr
      apply mem_cluster.mpr ((mem_cluster.mp hzcluster).trans ?_)
      apply IsOpenEdge.connected
      refine ⟨hopen.1, ?_⟩
      unfold rho removeSite bpt2_closeI
      have hnotTouch : s(z, w) ∉ bondFinsetTouch 2 n := by
        rw [hbx_mem_bondFinsetTouch_iff]
        simp [hopen.1, hzbox, hwbox]
      rw [if_neg hnot0, if_neg hnotTouch]
      exact hopenOmega



theorem bins_snd_data {x v : Site 2} (P : (hypercubicLattice 2).Walk x v)
    (hp : P.IsPath) (hv : v ≠ x) :
    (hypercubicLattice 2).Adj x P.snd ∧ P.snd ∈ P.support ∧ P.snd ≠ x := by
  cases P with
  | nil => exact absurd rfl hv
  | @cons x y v hxy Q =>
      have hsnd : (Walk.cons hxy Q).snd = y := by simp
      rw [hsnd]
      exact ⟨hxy, by simp, (hypercubicLattice 2).ne_of_adj hxy |>.symm⟩


theorem bins_branchSide_disjoint {n : ℕ} {B : Fin 3 → bins_Branch}
    (hbox : ∀ i z, z ∈ (B i).P.support → z ∈ box 2 n)
    (hpathDisj : ∀ i j, i ≠ j → ∀ z,
      z ∈ (B i).P.support → z ∈ (B j).P.support → z = ![0, 0])
    (huout : ∀ i, (B i).u ∉ box 2 n)
    {omega : ConfigSpace (Sym2 (Site 2))}
    (hclusterNe : ∀ i j, i ≠ j →
      cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i).u ≠
      cluster 2 (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B j).u)
    {i j : Fin 3} (hij : i ≠ j) :
    Disjoint
      (bins_branchSide (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B i))
      (bins_branchSide (removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)) (B j)) := by
  let rho := removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)
  rw [Set.disjoint_left]
  intro z hzi hzj
  rcases hzi with hpi | hci <;> rcases hzj with hpj | hcj
  · exact hpi.2 (hpathDisj i j hij z hpi.1 hpj.1)
  · exact (Set.disjoint_left.mp (bins_extCluster_avoids_box n omega (B j).u (huout j)))
      hcj (hbox i z hpi.1)
  · exact (Set.disjoint_left.mp (bins_extCluster_avoids_box n omega (B i).u (huout i)))
      hci (hbox j z hpj.1)
  · have hd : Disjoint (cluster 2 rho (B i).u) (cluster 2 rho (B j).u) := by
      rw [Set.disjoint_left]
      intro q hqi hqj
      apply hclusterNe i j hij
      exact cluster_eq_of_connected ((mem_cluster.mp hqi).trans (mem_cluster.mp hqj).symm)
    exact (Set.disjoint_left.mp hd) hci hcj



theorem bins_pattern_of_branches {n : ℕ} (B : Fin 3 → bins_Branch)
    (hp : ∀ i, (B i).P.IsPath)
    (hv : ∀ i, (B i).v ≠ ![0, 0])
    (hbox : ∀ i z, z ∈ (B i).P.support → z ∈ box 2 n)
    (hpathDisj : ∀ i j, i ≠ j → ∀ z,
      z ∈ (B i).P.support → z ∈ (B j).P.support → z = ![0, 0])
    (hadj : ∀ i, (hypercubicLattice 2).Adj (B i).v (B i).u)
    (huout : ∀ i, (B i).u ∉ box 2 n) :
    cylinder (bondFinsetTouch 2 n)
        ({bins_touchPattern n B} : Set
          (ConfigSpace (Subtype fun e => e ∈ bondFinsetTouch 2 n))) ∩
      bins_ExtEvent (bondFinsetTouch 2 n) (B 0).u (B 1).u (B 2).u ⊆
      NeighborTrifPrecursor 2 (B 0).P.snd (B 1).P.snd (B 2).P.snd := by
  rintro omega ⟨hcyl, hExt⟩
  let rho := removeSite 0 (bpt2_closeI (bondFinsetTouch 2 n) omega)
  change bins_ExtPred (B 0).u (B 1).u (B 2).u rho at hExt
  obtain ⟨⟨hinf0, hinf1, hinf2⟩, hne01, hne02, hne12⟩ := hExt
  have hclusterNe : ∀ i j : Fin 3, i ≠ j → cluster 2 rho (B i).u ≠ cluster 2 rho (B j).u := by
    intro i j hij
    fin_cases i
    · fin_cases j
      · contradiction
      · exact hne01
      · exact hne02
    · fin_cases j
      · exact fun h => hne01 h.symm
      · contradiction
      · exact hne12
    · fin_cases j
      · exact fun h => hne02 h.symm
      · exact fun h => hne12 h.symm
      · contradiction
  have hsnd (i : Fin 3) := bins_snd_data (B i).P (hp i) (hv i)
  have ha0 : (B 0).P.snd ∈ bins_branchSide rho (B 0) := Or.inl ⟨(hsnd 0).2.1, (hsnd 0).2.2⟩
  have ha1 : (B 1).P.snd ∈ bins_branchSide rho (B 1) := Or.inl ⟨(hsnd 1).2.1, (hsnd 1).2.2⟩
  have ha2 : (B 2).P.snd ∈ bins_branchSide rho (B 2) := Or.inl ⟨(hsnd 2).2.1, (hsnd 2).2.2⟩
  have hd01 := bins_branchSide_disjoint hbox hpathDisj huout hclusterNe
    (show (0 : Fin 3) ≠ 1 by decide)
  have hd02 := bins_branchSide_disjoint hbox hpathDisj huout hclusterNe
    (show (0 : Fin 3) ≠ 2 by decide)
  have hd12 := bins_branchSide_disjoint hbox hpathDisj huout hclusterNe
    (show (1 : Fin 3) ≠ 2 by decide)
  have hne : (B 0).P.snd ≠ (B 1).P.snd ∧ (B 0).P.snd ≠ (B 2).P.snd ∧
      (B 1).P.snd ≠ (B 2).P.snd := by
    exact ⟨fun h => Set.disjoint_left.mp hd01 ha0 (h ▸ ha1),
      fun h => Set.disjoint_left.mp hd02 ha0 (h ▸ ha2),
      fun h => Set.disjoint_left.mp hd12 ha1 (h ▸ ha2)⟩
  have hadj0 : (hypercubicLattice 2).Adj 0 (B 0).P.snd := by
    simpa [bcor_origin_eq] using (hsnd 0).1
  have hadj1 : (hypercubicLattice 2).Adj 0 (B 1).P.snd := by
    simpa [bcor_origin_eq] using (hsnd 1).1
  have hadj2 : (hypercubicLattice 2).Adj 0 (B 2).P.snd := by
    simpa [bcor_origin_eq] using (hsnd 2).1
  have hconn (i : Fin 3) : Connected 2 (removeSite 0 omega) (B i).P.snd (B i).u :=
    bins_branch_connected i (hp i) (hv i) (hadj i)
      (fun h => huout i (by simpa [h, mem_box])) hcyl (hbox i)
  have hle : rho ≤ removeSite 0 omega :=
    bpt2_removeSite_mono (bpt2_closeI_le (bondFinsetTouch 2 n) omega) 0
  have hinf (i : Fin 3) (hi : (cluster 2 rho (B i).u).Infinite) :
      (cluster 2 (removeSite 0 omega) (B i).P.snd).Infinite := by
    rw [cluster_eq_of_connected (hconn i)]
    exact hi.mono (cluster_mono hle (B i).u)
  apply bins_precursor_of_sides omega (B 0).P.snd (B 1).P.snd (B 2).P.snd
    hne ⟨hadj0, hadj1, hadj2⟩
    (bins_branchSide rho (B 0)) (bins_branchSide rho (B 1)) (bins_branchSide rho (B 2))
    ⟨ha0, ha1, ha2⟩ ⟨hd01, hd02, hd12⟩
  · exact ⟨bins_branchSide_openClosed hbox hpathDisj hadj huout hcyl hclusterNe 0,
      bins_branchSide_openClosed hbox hpathDisj hadj huout hcyl hclusterNe 1,
      bins_branchSide_openClosed hbox hpathDisj hadj huout hcyl hclusterNe 2⟩
  · exact ⟨hinf 0 hinf0, hinf 1 hinf1, hinf 2 hinf2⟩





theorem bins_routePackage_of_nineShell_measure
    (mu : Measure (ConfigSpace (Sym2 (Site 2)))) (m : ℕ)
    (v u : Fin 9 → Site 2)
    (hpos : 0 < mu (bins_NineShellEvent m v u)) :
    ∃ (I : Finset (Sym2 (Site 2))) (eta : ConfigSpace ↥I) (a1 a2 a3 : Site 2)
      (X : Set (ConfigSpace (Sym2 (Site 2)))),
      (a1 ≠ a2 ∧ a1 ≠ a3 ∧ a2 ≠ a3) ∧
      ((hypercubicLattice 2).Adj 0 a1 ∧ (hypercubicLattice 2).Adj 0 a2 ∧
        (hypercubicLattice 2).Adj 0 a3) ∧
      MeasurableSet X ∧ DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ) ∧
      0 < mu X ∧
      cylinder I ({eta} : Set (ConfigSpace ↥I)) ∩ X ⊆
        NeighborTrifPrecursor 2 a1 a2 a3 := by
  obtain ⟨omega, homega⟩ := nonempty_of_measure_ne_zero (ne_of_gt hpos)
  obtain ⟨i, j, k, hij, hik, hjk, hvij, hvik, hvjk, hside⟩ :=
    bins_NineShellEvent_three_same_side homega
  obtain ⟨hgeom, hinf, hdist⟩ := homega
  have huout (q : Fin 9) : u q ∉ box 2 m := by
    have hi : (cluster 2 (removeSites (boxFinset 2 m) omega) (u q)).Infinite := by
      rw [← bins_cluster_closeTouch_eq_removeBox]
      exact hinf q
    exact fun h => stac_infiniteCluster_notMem (boxFinset 2 m) omega hi
      (mem_boxFinset.mpr h)
  have hm : 1 ≤ m := by
    by_contra h
    have hm0 : m = 0 := by omega
    subst m
    have hi0 : v i = 0 := by
      rw [← Set.mem_singleton_iff, ← bc24_box_zero 2]
      exact (hgeom i).1
    have hj0 : v j = 0 := by
      rw [← Set.mem_singleton_iff, ← bc24_box_zero 2]
      exact (hgeom j).1
    exact hvij (hi0.trans hj0.symm)
  have hC := bins_corridors_of_same_side m hm (v i) (v j) (v k)
    (hgeom i).1 (hgeom j).1 (hgeom k).1 hvij hvik hvjk hside
  obtain ⟨P0, P1, P2, hp0, hp1', hp2, hb0, hb1, hb2, hd01, hd02, hd12⟩ := hC
  let B : Fin 3 → bins_Branch := ![
    ⟨v i, u i, P0⟩, ⟨v j, u j, P1⟩, ⟨v k, u k, P2⟩]
  have hBpath : ∀ q, (B q).P.IsPath := by intro q; fin_cases q <;> simp [B, hp0, hp1', hp2]
  have hBbox : ∀ q z, z ∈ (B q).P.support → z ∈ box 2 m := by
    intro q z hz
    fin_cases q
    · exact hb0 z (by simpa [B] using hz)
    · exact hb1 z (by simpa [B] using hz)
    · exact hb2 z (by simpa [B] using hz)
  have hBdisj : ∀ q r, q ≠ r → ∀ z,
      z ∈ (B q).P.support → z ∈ (B r).P.support → z = ![0, 0] := by
    intro q r hqr z hzq hzr
    fin_cases q
    · fin_cases r
      · contradiction
      · exact hd01 z (by simpa [B] using hzq) (by simpa [B] using hzr)
      · exact hd02 z (by simpa [B] using hzq) (by simpa [B] using hzr)
    · fin_cases r
      · exact hd01 z (by simpa [B] using hzr) (by simpa [B] using hzq)
      · contradiction
      · exact hd12 z (by simpa [B] using hzq) (by simpa [B] using hzr)
    · fin_cases r
      · exact hd02 z (by simpa [B] using hzr) (by simpa [B] using hzq)
      · exact hd12 z (by simpa [B] using hzr) (by simpa [B] using hzq)
      · contradiction
  have hBadj : ∀ q, (hypercubicLattice 2).Adj (B q).v (B q).u := by
    intro q; fin_cases q
    · simpa [B] using (hgeom i).2
    · simpa [B] using (hgeom j).2
    · simpa [B] using (hgeom k).2
  have hBout : ∀ q, (B q).u ∉ box 2 m := by
    intro q; fin_cases q
    · simpa [B] using huout i
    · simpa [B] using huout j
    · simpa [B] using huout k
  have hBv : ∀ q, (B q).v ≠ ![0, 0] := by
    intro q
    fin_cases q <;> simp [B] <;> intro h
    all_goals
      have hs := hside
      simp only [h, Matrix.cons_val_zero, Matrix.cons_val_one] at hs
      omega
  have hsubset : bins_NineShellEvent m v u ⊆
      bins_ExtEvent (bondFinsetTouch 2 m) (u i) (u j) (u k) := by
    intro xi hxi
    obtain ⟨_, hxiInf, hxiDist⟩ := hxi
    exact ⟨⟨hxiInf i, hxiInf j, hxiInf k⟩,
      hxiDist i j hij, hxiDist i k hik, hxiDist j k hjk⟩
  have hXpos : 0 < mu (bins_ExtEvent (bondFinsetTouch 2 m) (u i) (u j) (u k)) :=
    lt_of_lt_of_le hpos (measure_mono hsubset)
  have hpattern := bins_pattern_of_branches B hBpath hBv hBbox hBdisj hBadj hBout
  have hsnd (q : Fin 3) := bins_snd_data (B q).P (hBpath q) (hBv q)
  have hne : (B 0).P.snd ≠ (B 1).P.snd ∧ (B 0).P.snd ≠ (B 2).P.snd ∧
      (B 1).P.snd ≠ (B 2).P.snd := by
    refine ⟨?_, ?_, ?_⟩
    · intro h; exact (hsnd 0).2.2 (hBdisj 0 1 (by decide) _ (hsnd 0).2.1 (h ▸ (hsnd 1).2.1))
    · intro h; exact (hsnd 0).2.2 (hBdisj 0 2 (by decide) _ (hsnd 0).2.1 (h ▸ (hsnd 2).2.1))
    · intro h; exact (hsnd 1).2.2 (hBdisj 1 2 (by decide) _ (hsnd 1).2.1 (h ▸ (hsnd 2).2.1))
  have hsadj : (hypercubicLattice 2).Adj 0 (B 0).P.snd ∧
      (hypercubicLattice 2).Adj 0 (B 1).P.snd ∧
      (hypercubicLattice 2).Adj 0 (B 2).P.snd := by
    refine ⟨?_, ?_, ?_⟩
    · rw [← bcor_origin_eq]; exact (hsnd 0).1
    · rw [← bcor_origin_eq]; exact (hsnd 1).1
    · rw [← bcor_origin_eq]; exact (hsnd 2).1
  refine ⟨bondFinsetTouch 2 m, bins_touchPattern m B,
    (B 0).P.snd, (B 1).P.snd, (B 2).P.snd,
    bins_ExtEvent (bondFinsetTouch 2 m) (u i) (u j) (u k),
    hne, hsadj, bins_ExtEvent_measurable _ _ _ _, bins_ExtEvent_dependsOn _ _ _ _,
    ?_, ?_⟩
  · exact hXpos
  · simpa [B] using hpattern


theorem bins_routePackage_of_nineShell (p : ℝ≥0) (hp1 : p ≤ 1) (m : ℕ)
    (v u : Fin 9 → Site 2)
    (hpos : 0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      (bins_NineShellEvent m v u)) :
    ∃ (I : Finset (Sym2 (Site 2))) (eta : ConfigSpace ↥I) (a1 a2 a3 : Site 2)
      (X : Set (ConfigSpace (Sym2 (Site 2)))),
      (a1 ≠ a2 ∧ a1 ≠ a3 ∧ a2 ≠ a3) ∧
      ((hypercubicLattice 2).Adj 0 a1 ∧ (hypercubicLattice 2).Adj 0 a2 ∧
        (hypercubicLattice 2).Adj 0 a3) ∧
      MeasurableSet X ∧ DependsOn X ((↑I : Set (Sym2 (Site 2)))ᶜ) ∧
      0 < bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 X ∧
      cylinder I ({eta} : Set (ConfigSpace ↥I)) ∩ X ⊆
        NeighborTrifPrecursor 2 a1 a2 a3 :=
  bins_routePackage_of_nineShell_measure
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1) m v u hpos



theorem bins_route (p : ℝ≥0) (hp1 : p ≤ 1) : bins_Route p hp1 := by
  intro n hpos
  obtain ⟨m, v, u, hNine⟩ := bins_exists_NineShellEvent_pos_of_threeMeetBox p hp1 n hpos
  exact bins_routePackage_of_nineShell p hp1 m v u hNine



theorem bins_bk_unconditional (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p) (hplt : p < 1) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {omega | numInfiniteClusters 2 omega = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {omega | numInfiniteClusters 2 omega = 1} = 1) ∧
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 ∧
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {omega | numInfiniteClusters 2 omega ≤ 1} = 1 :=
  bins_bk p hp1 hp0 hplt (bins_route p hp1)

end StatMech.Walls
