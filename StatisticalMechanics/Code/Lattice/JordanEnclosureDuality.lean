/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.JordanZ2
import Code.Lattice.JordanEnclosure
import Code.Lattice.CrossingParity
import Code.Lattice.WhitneyBridge
import Code.Lattice.WhitneyCorrect
import Code.Lattice.JordanEvenClose
import Code.Lattice.JordanEvenBiconditional
import Code.Lattice.JordanKeepReconnect
import Code.Lattice.JordanFiniteDetour
import Code.Lattice.JordanEulerInduction
import Code.Lattice.JordanWindingClose

open SimpleGraph Set

namespace StatMech

namespace Lattice











def jed_cutSet (T : Site 2 → Prop) : Set (Sym2 (Site 2)) :=
  {e | ∃ a b : Site 2, (hypercubicLattice 2).Adj a b ∧ e = sharedPrimalEdge a b ∧ (T a ↔ ¬ T b)}




theorem jed_mem_cutSet_iff (T : Site 2 → Prop) {c d : Site 2}
    (hcd : (hypercubicLattice 2).Adj c d) :
    sharedPrimalEdge c d ∈ jed_cutSet T ↔ (T c ↔ ¬ T d) := by
  constructor
  · rintro ⟨a, b, hab, heq, hsplit⟩
    have hsy : s(c, d) = s(a, b) := (jce_sharedPrimalEdge_inj hcd hab).mpr heq
    rw [Sym2.eq_iff] at hsy
    rcases hsy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hsplit
    · tauto
  · intro h; exact ⟨c, d, hcd, rfl, h⟩









theorem jed_sh_right (x y : ℤ) :
    sharedPrimalEdge ![x, y] ![x, y - 1] = s(![x, y], ![x + 1, y]) := by
  rw [sharedPrimalEdge_bottom]; unfold faceCorner00 faceCorner10; norm_num


theorem jed_sh_left (x y : ℤ) :
    sharedPrimalEdge ![x - 1, y] ![x - 1, y - 1] = s(![x - 1, y], ![x, y]) := by
  rw [sharedPrimalEdge_bottom]; unfold faceCorner00 faceCorner10; rw [show (x - 1) + 1 = x by ring]


theorem jed_sh_up (x y : ℤ) :
    sharedPrimalEdge ![x, y] ![x - 1, y] = s(![x, y], ![x, y + 1]) := by
  rw [sharedPrimalEdge_left]; unfold faceCorner00 faceCorner01; norm_num


theorem jed_sh_down (x y : ℤ) :
    sharedPrimalEdge ![x, y - 1] ![x - 1, y - 1] = s(![x, y - 1], ![x, y]) := by
  rw [sharedPrimalEdge_left]; unfold faceCorner00 faceCorner01; rw [show (y - 1) + 1 = y by ring]












theorem jed_cutSet_even (T : Site 2 → Prop) (v : Site 2) :
    Even (jce_degree (jed_cutSet T) v) := by
  classical
  set x := v 0 with hx
  set y := v 1 with hy
  have hv : v = ![x, y] := by funext i; fin_cases i <;> rfl
  rw [jce_degree, Finset.card_filter, Fin.sum_univ_four]
  simp only [jce_nbr, hv, Matrix.cons_val_zero, Matrix.cons_val_one]
  have m0 : (s(![x, y], ![x + 1, y]) ∈ jed_cutSet T) ↔ (T ![x, y] ↔ ¬ T ![x, y - 1]) := by
    rw [← jed_sh_right x y]; exact jed_mem_cutSet_iff T (latAdj_bottom x y)
  have m1 : (s(![x, y], ![x - 1, y]) ∈ jed_cutSet T) ↔ (T ![x - 1, y] ↔ ¬ T ![x - 1, y - 1]) := by
    rw [show s(![x, y], ![x - 1, y]) = s(![x - 1, y], ![x, y]) from Sym2.eq_swap, ← jed_sh_left x y]
    exact jed_mem_cutSet_iff T (latAdj_bottom (x - 1) y)
  have m2 : (s(![x, y], ![x, y + 1]) ∈ jed_cutSet T) ↔ (T ![x, y] ↔ ¬ T ![x - 1, y]) := by
    rw [← jed_sh_up x y]; exact jed_mem_cutSet_iff T (latAdj_left x y)
  have m3 : (s(![x, y], ![x, y - 1]) ∈ jed_cutSet T) ↔ (T ![x, y - 1] ↔ ¬ T ![x - 1, y - 1]) := by
    rw [show s(![x, y], ![x, y - 1]) = s(![x, y - 1], ![x, y]) from Sym2.eq_swap, ← jed_sh_down x y]
    exact jed_mem_cutSet_iff T (latAdj_left x (y - 1))
  rw [m0, m1, m2, m3, Nat.even_iff]
  by_cases hA : T ![x, y] <;> by_cases hB : T ![x, y - 1] <;> by_cases hC : T ![x - 1, y - 1] <;>
    by_cases hD : T ![x - 1, y] <;>
    simp only [hA, hB, hC, hD, not_true, not_false_iff, iff_true, iff_false] <;> norm_num









def jed_primalGraph (E : Set (Sym2 (Site 2))) : SimpleGraph (Site 2) where
  Adj u w := (hypercubicLattice 2).Adj u w ∧ s(u, w) ∈ E
  symm := by rintro u w ⟨h1, h2⟩; exact ⟨h1.symm, by rwa [Sym2.eq_swap]⟩
  loopless := ⟨fun u h => (hypercubicLattice 2).irrefl h.1⟩

@[simp] theorem jed_primalGraph_adj (E : Set (Sym2 (Site 2))) (u w : Site 2) :
    (jed_primalGraph E).Adj u w ↔ (hypercubicLattice 2).Adj u w ∧ s(u, w) ∈ E := Iff.rfl


theorem jed_primalGraph_le (E : Set (Sym2 (Site 2))) : jed_primalGraph E ≤ hypercubicLattice 2 :=
  fun _ _ h => h.1


theorem jed_primalGraph_edgeSet_subset (E : Set (Sym2 (Site 2))) :
    (jed_primalGraph E).edgeSet ⊆ E := by
  intro e he; induction e with
  | h u w => rw [SimpleGraph.mem_edgeSet] at he; exact he.2


noncomputable instance jed_primalGraph_locallyFinite (E : Set (Sym2 (Site 2))) :
    SimpleGraph.LocallyFinite (jed_primalGraph E) := fun _ =>
  Set.Finite.fintype (Set.Finite.subset (Set.toFinite _) (fun _ hw =>
    (SimpleGraph.mem_neighborSet _ _ _).mpr (jed_primalGraph_le E hw)))


theorem jed_nbr_adj (v : Site 2) (i : Fin 4) : (hypercubicLattice 2).Adj v (jce_nbr v i) := by
  fin_cases i <;>
    · simp only [jce_nbr]
      rw [hypercubicLattice_adj, Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]; norm_num




theorem jed_jce_degree_primalGraph (E : Set (Sym2 (Site 2))) (v : Site 2) :
    jce_degree (jed_primalGraph E).edgeSet v = jce_degree E v := by
  classical
  rw [jce_degree, jce_degree]
  congr 1
  apply Finset.filter_congr
  intro i _
  have : (s(v, jce_nbr v i) ∈ (jed_primalGraph E).edgeSet) ↔ (s(v, jce_nbr v i) ∈ E) := by
    rw [SimpleGraph.mem_edgeSet]; exact ⟨fun h => h.2, fun h => ⟨jed_nbr_adj v i, h⟩⟩
  simp only [this]



theorem jed_degree_primalGraph (E : Set (Sym2 (Site 2))) (v : Site 2) :
    (jed_primalGraph E).degree v = jce_degree E v := by
  rw [← jed_jce_degree_primalGraph E v, jeb_jce_degree_eq_degree (jed_primalGraph E)
    (jed_primalGraph_le E) v]











theorem jed_wall_mem_cutSet (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    sharedPrimalEdge f0 g0 ∈
      jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v) := by
  rw [jed_mem_cutSet_iff _ hfg]
  exact ⟨fun _ => hsep, fun _ => Reachable.refl f0⟩





theorem jed_cutSet_subset (H : SimpleGraph (Site 2)) (f0 g0 : Site 2)
    (hfg : (hypercubicLattice 2).Adj f0 g0) :
    jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v) ⊆
      insert (sharedPrimalEdge f0 g0) H.edgeSet := by
  rintro e ⟨a, b, hab, rfl, hsplit⟩
  have hnotadj : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Adj a b := by
    intro hadj
    have : ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 a ↔
        ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 b :=
      ⟨fun h => h.trans hadj.reachable, fun h => h.trans hadj.symm.reachable⟩
    tauto
  by_cases hwall : s(a, b) = s(f0, g0)
  · rw [(jce_sharedPrimalEdge_inj hab hfg).mp hwall]; exact Set.mem_insert _ _
  · refine Set.mem_insert_of_mem _ ?_
    rw [deleteEdges_adj, Set.mem_singleton_iff, not_and_or, not_not] at hnotadj
    rcases hnotadj with hnwhb | hw
    · rw [whb_faceRegion_adj, not_and_or] at hnwhb
      rcases hnwhb with hnl | hns
      · exact absurd hab hnl
      · rw [not_not] at hns; exact hns
    · exact absurd hw hwall










theorem jed_cutMinusWall_degree_data (H : SimpleGraph (Site 2)) (p q f0 g0 : Site 2)
    (hpq : (hypercubicLattice 2).Adj p q) (hfg : (hypercubicLattice 2).Adj f0 g0)
    (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    Odd (jce_degree
        (jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v)
          \ {s(p, q)}) p) ∧
      Odd (jce_degree
        (jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v)
          \ {s(p, q)}) q) ∧
      (∀ v, v ≠ p → v ≠ q → Even (jce_degree
        (jed_cutSet (fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v)
          \ {s(p, q)}) v)) := by
  classical
  set T := fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v with hT
  set E := jed_cutSet T with hE
  set E' := E \ {s(p, q)} with hE'
  
  have hwallE : s(p, q) ∈ E := by
    rw [hE, ← hshared]; exact jed_wall_mem_cutSet H f0 g0 hfg hsep
  have hwallnE' : s(p, q) ∉ E' := fun h => h.2 rfl
  have hinsert : insert (s(p, q)) E' = E := by
    rw [hE', Set.insert_diff_singleton, Set.insert_eq_self.mpr hwallE]
  
  have hEeven : ∀ v, Even (jce_degree E v) := fun v => jed_cutSet_even T v
  have hqp : s(q, p) ∉ E' := fun h => hwallnE' (by rwa [Sym2.eq_swap] at h)
  refine ⟨?_, ?_, ?_⟩
  · have hd := jeb_jce_degree_insert_endpoint E' p q hpq hwallnE'
    rw [hinsert] at hd
    have := hEeven p; rw [hd, Nat.even_add_one, Nat.not_even_iff_odd] at this; exact this
  · have hd := jeb_jce_degree_insert_endpoint E' q p hpq.symm hqp
    rw [show s(q, p) = s(p, q) from Sym2.eq_swap, hinsert] at hd
    have := hEeven q; rw [hd, Nat.even_add_one, Nat.not_even_iff_odd] at this; exact this
  · intro v hvp hvq
    have hd := jeb_jce_degree_insert_other E' p q v hvp hvq
    rw [hinsert] at hd
    have := hEeven v; rwa [hd] at this















theorem jed_reachable_of_separated (H : SimpleGraph (Site 2)) (hfin : H.edgeSet.Finite)
    (p q f0 g0 : Site 2) (hpq : (hypercubicLattice 2).Adj p q) (_hnpq : s(p, q) ∉ H.edgeSet)
    (hfg : (hypercubicLattice 2).Adj f0 g0) (hshared : sharedPrimalEdge f0 g0 = s(p, q))
    (hsep : ¬ ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 g0) :
    H.Reachable p q := by
  classical
  set T := fun v => ((whb_faceRegion H).deleteEdges {s(f0, g0)}).Reachable f0 v with hT
  set E := jed_cutSet T with hE
  set E' := E \ {s(p, q)} with hE'
  set K := jed_primalGraph E' with hK
  
  have hEsub : E ⊆ insert (sharedPrimalEdge f0 g0) H.edgeSet := jed_cutSet_subset H f0 g0 hfg
  rw [hshared] at hEsub
  have hE'sub : E' ⊆ H.edgeSet := by
    intro e he
    rcases hEsub he.1 with h | h
    · exact absurd (h ▸ Set.mem_singleton _ : e ∈ ({s(p, q)} : Set _)) he.2
    · exact h
  
  have hKleH : K ≤ H := by
    intro u w hadj
    have hmem : s(u, w) ∈ E' := hadj.2
    exact (SimpleGraph.mem_edgeSet H).mp (hE'sub hmem)
  
  have hHsupp : H.support.Finite := by
    haveI : Fintype H.edgeSet := hfin.fintype
    exact jeb_support_finite_of_edgeSet H
  have hKsuppSub : K.support ⊆ H.support := by
    intro v hv
    rw [SimpleGraph.mem_support] at hv ⊢
    obtain ⟨w, hw⟩ := hv
    exact ⟨w, hKleH hw⟩
  have hKsupp : K.support.Finite := hHsupp.subset hKsuppSub
  
  obtain ⟨hop, hoq, hoth⟩ :=
    jed_cutMinusWall_degree_data H p q f0 g0 hpq hfg hshared hsep
  have hdeg : ∀ v, K.degree v = jce_degree E' v := fun v => jed_degree_primalGraph E' v
  have hKp : Odd (K.degree p) := by rw [hdeg]; exact hop
  have hKq : Odd (K.degree q) := by rw [hdeg]; exact hoq
  have hKoth : ∀ v, v ≠ p → v ≠ q → Even (K.degree v) := by
    intro v hvp hvq; rw [hdeg]; exact hoth v hvp hvq
  
  have hKreach : K.Reachable p q := jeb_two_odd_reachable K hKsupp p q hKp hKq hKoth
  exact hKreach.mono hKleH













theorem jed_finiteKeepReconnect : jkr_FiniteKeepReconnectResidue := by
  intro H p q f0 g0 hfin hpq hnpq hfg hshared hnr
  by_contra hsep
  exact hnr (jed_reachable_of_separated H hfin p q f0 g0 hpq hnpq hfg hshared hsep)


theorem jed_sameComponentResidue : jfd_SameComponentResidue :=
  jfd_sameComponent_iff_finiteKeep.mpr jed_finiteKeepReconnect













theorem jed_keepResidue (P : PlanarZ2Subgraph) : jwc_KeepResidue P := by
  intro K hKle x y hadjG hnotK f0 g0 hfg hshared hnr
  have hfin : (jei_pushGraph P K).edgeSet.Finite := jei_pushGraph_edgeSet_finite P K
  have hpq : (hypercubicLattice 2).Adj (P.emb x) (P.emb y) := P.isSub hadjG
  have hnpq : s(P.emb x, P.emb y) ∉ (jei_pushGraph P K).edgeSet :=
    jkd_wall_not_mem_pushGraph P K hnotK
  have hnrpush : ¬ (jei_pushGraph P K).Reachable (P.emb x) (P.emb y) := by
    rw [jei_push_reachable_iff]; exact hnr
  exact jed_finiteKeepReconnect (jei_pushGraph P K) (P.emb x) (P.emb y) f0 g0
    hfin hpq hnpq hfg hshared hnrpush








theorem jed_faithfulDiscreteJordan (P : PlanarZ2Subgraph) : whc_FaithfulDiscreteJordan P :=
  jwc_faithfulDiscreteJordan_of_keepResidue P (jed_keepResidue P)










theorem jed_not_reachable_of_isolated (H : SimpleGraph (Site 2)) (u v : Site 2)
    (hiso : ∀ w, ¬ H.Adj u w) (hne : u ≠ v) : ¬ H.Reachable u v := by
  rintro ⟨w⟩
  cases w with
  | nil => exact hne rfl
  | cons hadj _ => exact hiso _ hadj





noncomputable def jed_boxEdges : Finset (Sym2 (Site 2)) :=
  { s(![(-1:ℤ), -2], ![0, -2]), s(![(0:ℤ), -2], ![1, -2]), s(![(1:ℤ), -2], ![2, -2]),
    s(![(-1:ℤ), 1], ![0, 1]), s(![(0:ℤ), 1], ![1, 1]), s(![(1:ℤ), 1], ![2, 1]),
    s(![(-1:ℤ), -2], ![-1, -1]), s(![(-1:ℤ), -1], ![-1, 0]), s(![(-1:ℤ), 0], ![-1, 1]),
    s(![(2:ℤ), -2], ![2, -1]), s(![(2:ℤ), -1], ![2, 0]), s(![(2:ℤ), 0], ![2, 1]) }


noncomputable def jed_boxH : SimpleGraph (Site 2) :=
  jed_primalGraph (jed_boxEdges : Set (Sym2 (Site 2)))


theorem jed_boxH_iso_p (w : Site 2) : ¬ jed_boxH.Adj ![(0:ℤ), 0] w := by
  rw [jed_boxH, jed_primalGraph_adj]
  rintro ⟨_, hmem⟩
  rw [Finset.mem_coe] at hmem
  simp only [jed_boxEdges, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, site2_eq] at hmem
  omega


theorem jed_boxH_iso_q (w : Site 2) : ¬ jed_boxH.Adj ![(1:ℤ), 0] w := by
  rw [jed_boxH, jed_primalGraph_adj]
  rintro ⟨_, hmem⟩
  rw [Finset.mem_coe] at hmem
  simp only [jed_boxEdges, Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff, site2_eq] at hmem
  omega


theorem jed_boxH_edgeSet_finite : jed_boxH.edgeSet.Finite :=
  (jed_boxEdges.finite_toSet).subset (jed_primalGraph_edgeSet_subset _)








theorem jed_enclosingBox_witness :
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ jed_boxH.edgeSet ∧
    (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∧
    ¬ jed_boxH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] ∧
    ((whb_faceRegion jed_boxH).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] := by
  have hpq : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(1:ℤ), 0] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have hfg : (hypercubicLattice 2).Adj ![(0:ℤ), 0] ![(0:ℤ), -1] := by
    rw [hypercubicLattice_adj, Fin.sum_univ_two]; norm_num
  have hshared : sharedPrimalEdge ![(0:ℤ), 0] ![(0:ℤ), -1] = s(![(0:ℤ), 0], ![(1:ℤ), 0]) := by
    rw [show (![(0:ℤ), -1] : Site 2) = ![(0:ℤ), 0 - 1] by norm_num, sharedPrimalEdge_bottom]
    unfold faceCorner00 faceCorner10; norm_num
  have hnpq : s(![(0:ℤ), 0], ![(1:ℤ), 0]) ∉ jed_boxH.edgeSet := by
    rw [SimpleGraph.mem_edgeSet]; exact jed_boxH_iso_p _
  have hnr : ¬ jed_boxH.Reachable ![(0:ℤ), 0] ![(1:ℤ), 0] :=
    jed_not_reachable_of_isolated jed_boxH _ _ jed_boxH_iso_p (by
      rw [ne_eq, site2_eq]; norm_num)
  refine ⟨hpq, hnpq, hfg, hshared, hnr, ?_⟩
  exact jed_finiteKeepReconnect jed_boxH ![(0:ℤ), 0] ![(1:ℤ), 0] ![(0:ℤ), 0] ![(0:ℤ), -1]
    jed_boxH_edgeSet_finite hpq hnpq hfg hshared hnr







theorem jed_witnesses :
    ((whb_faceRegion (⊥ : SimpleGraph (Site 2))).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    ((whb_faceRegion (jei_pushGraph jbc_Pce ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    ((whb_faceRegion (jei_pushGraph jkd_ringP ⊥)).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    ((whb_faceRegion jed_boxH).deleteEdges
      {s(![(0:ℤ), 0], ![(0:ℤ), -1])}).Reachable ![(0:ℤ), 0] ![(0:ℤ), -1] ∧
    jkr_lineH.edgeSet.Infinite :=
  ⟨(jkr_witness_bot).2.2.2.2.2, (jkr_witness_square).2.2.2.2.2,
    (jkr_witness_ring).2.2.2.2.2, jed_enclosingBox_witness.2.2.2.2.2,
    jkr_lineH_edgeSet_infinite⟩


















theorem jed_status :
    (∀ (T : Site 2 → Prop) (v : Site 2), Even (jce_degree (jed_cutSet T) v)) ∧
    jkr_FiniteKeepReconnectResidue ∧
    jfd_SameComponentResidue ∧
    (∀ P : PlanarZ2Subgraph, whc_FaithfulDiscreteJordan P) :=
  ⟨jed_cutSet_even, jed_finiteKeepReconnect, jed_sameComponentResidue, jed_faithfulDiscreteJordan⟩

end Lattice

end StatMech
