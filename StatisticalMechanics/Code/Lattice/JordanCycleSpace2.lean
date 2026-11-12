/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































import Mathlib
import Code.Lattice.HypercubicLattice
import Code.Lattice.PlanarDual
import Code.Lattice.PlanarFaceGeometric
import Code.Lattice.JordanEnclosure
import Code.Lattice.EulerFaces2
import Code.Lattice.JordanEulerInduction
import Code.Lattice.WhitneyBridge
import Code.Lattice.JordanEvenClose
import Code.Lattice.JordanEvenBiconditional
import Code.Lattice.JordanFaithfulCount

open SimpleGraph Set

namespace StatMech

namespace Lattice






theorem jcx_faceCount_eq_nullity_add_one {V : Type*} [Finite V] [DecidableEq V]
    (K : SimpleGraph V) : faceCount K = nullity K + 1 := rfl



theorem jcx_nullity_bot {V : Type*} [Finite V] [DecidableEq V] :
    nullity (⊥ : SimpleGraph V) = 0 :=
  nullity_eq_zero_of_isAcyclic (isAcyclic_bot)




theorem jcx_whb_bot_card :
    Nat.card (whb_faceRegion (⊥ : SimpleGraph (Site 2))).ConnectedComponent = 1 := by
  rw [jfc_whb_bot]
  have hreach : ∀ a b : Site 2, (hypercubicLattice 2).Reachable a b :=
    fun a b => pbs_reach_all a b
  have hsub : Subsingleton (hypercubicLattice 2).ConnectedComponent :=
    ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hreach a b))⟩
  haveI : Nonempty (hypercubicLattice 2).ConnectedComponent :=
    ⟨(hypercubicLattice 2).connectedComponentMk ![0, 0]⟩
  rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, inferInstance⟩






















def jcx_EvenCountResidue (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K : SimpleGraph P.V), K ≤ P.G →
    jce_ClosedContour (jei_pushGraph P K).edgeSet →
    Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent = faceCount K




theorem jcx_whb_total_count_of_evenResidue (P : PlanarZ2Subgraph)
    (hP : jeb_EvenDegreeSubgraph P) (hres : jcx_EvenCountResidue P) :
    Nat.card (whb_faceRegion (imageGraph P)).ConnectedComponent = faceCount P.G := by
  have hcc : jce_ClosedContour (jei_pushGraph P P.G).edgeSet := by
    rw [jei_pushGraph_G P]; exact hP
  have h := hres P.G le_rfl hcc
  rwa [jei_pushGraph_G P] at h






theorem jcx_faithfulRegionCount_eq_nullity_of_evenResidue (P : PlanarZ2Subgraph)
    (hP : jeb_EvenDegreeSubgraph P) (hres : jcx_EvenCountResidue P) :
    whc_faithfulRegionCount P = nullity P.G := by
  have htot := jcx_whb_total_count_of_evenResidue P hP hres
  have hcard := jfc_whb_bounded_add_one_eq_card P
  rw [htot, faceCount] at hcard
  omega







theorem jcx_faithfulDiscreteJordan_of_evenResidue (P : PlanarZ2Subgraph)
    (hP : jeb_EvenDegreeSubgraph P) (hres : jcx_EvenCountResidue P) :
    whc_FaithfulDiscreteJordan P := by
  classical
  haveI : Finite (whb_faceRegion (imageGraph P)).ConnectedComponent :=
    jfc_whb_regionComponents_finite (imageGraph P) (Set.toFinite (imageGraph P).edgeSet)
  have heq : whc_faithfulRegionCount P = nullity P.G :=
    jcx_faithfulRegionCount_eq_nullity_of_evenResidue P hP hres
  unfold whc_faithfulRegionCount at heq
  exact ⟨Finite.equivFinOfCardEq heq⟩




theorem jcx_faithfulCountResidue_of_evenResidue
    (h : ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P → jcx_EvenCountResidue P) :
    jeb_FaithfulCountResidue :=
  fun P hP => jcx_faithfulDiscreteJordan_of_evenResidue P hP (h P hP)































def jcx_EvenPeel (P : PlanarZ2Subgraph) : Prop :=
  ∀ (K : SimpleGraph P.V), K ≤ P.G → jce_ClosedContour (jei_pushGraph P K).edgeSet →
    K ≠ ⊥ →
    ∃ K' : SimpleGraph P.V, K' ≤ P.G ∧ jce_ClosedContour (jei_pushGraph P K').edgeSet ∧
      K'.edgeSet.ncard < K.edgeSet.ncard ∧
      faceCount K' + 1 = faceCount K ∧
      Nat.card (whb_faceRegion (jei_pushGraph P K)).ConnectedComponent
        = Nat.card (whb_faceRegion (jei_pushGraph P K')).ConnectedComponent + 1








theorem jcx_evenCountResidue_of_evenPeel (P : PlanarZ2Subgraph) (hpeel : jcx_EvenPeel P) :
    jcx_EvenCountResidue P := by
  classical
  haveI hVfin : Finite P.V := P.finV
  haveI hVdec : DecidableEq P.V := P.decV
  intro K
  generalize hn : K.edgeSet.ncard = n
  induction n using Nat.strong_induction_on generalizing K with
  | _ n ih =>
    intro hKle hcc
    rcases Nat.eq_zero_or_pos n with hz | hpos
    · 
      subst hz
      have hempty : K.edgeSet = ∅ := (Set.ncard_eq_zero (Set.toFinite K.edgeSet)).mp hn
      have hbot : K = ⊥ := by rw [← edgeSet_eq_empty]; exact hempty
      subst hbot
      rw [jei_pushGraph_bot, jfc_whb_bot]
      have hlat : Nat.card (hypercubicLattice 2).ConnectedComponent = 1 := by
        have hreach : ∀ a b : Site 2, (hypercubicLattice 2).Reachable a b :=
          fun a b => pbs_reach_all a b
        have hsub : Subsingleton (hypercubicLattice 2).ConnectedComponent :=
          ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hreach a b))⟩
        haveI : Nonempty (hypercubicLattice 2).ConnectedComponent :=
          ⟨(hypercubicLattice 2).connectedComponentMk ![0, 0]⟩
        rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, inferInstance⟩
      rw [hlat]
      unfold faceCount nullity
      rw [SimpleGraph.edgeSet_bot, Set.ncard_empty, card_components_bot]; simp
    · 
      have hKne : K ≠ ⊥ := by
        intro hbot
        rw [hbot, SimpleGraph.edgeSet_bot, Set.ncard_empty] at hn
        omega
      obtain ⟨K', hK'le, hcc', hlt, hface, hdual⟩ := hpeel K hKle hcc hKne
      have ihK' : Nat.card (whb_faceRegion (jei_pushGraph P K')).ConnectedComponent
          = faceCount K' := by
        have hlt' : K'.edgeSet.ncard < n := by rw [← hn]; exact hlt
        exact ih K'.edgeSet.ncard hlt' K' rfl hK'le hcc'
      rw [hdual, ihK']
      omega







theorem jcx_faithfulCountResidue_of_evenPeel
    (h : ∀ (P : PlanarZ2Subgraph), jeb_EvenDegreeSubgraph P → jcx_EvenPeel P) :
    jeb_FaithfulCountResidue :=
  jcx_faithfulCountResidue_of_evenResidue
    (fun P hP => jcx_evenCountResidue_of_evenPeel P (h P hP))






















theorem jcx_square_dual_card :
    Nat.card (whb_faceRegion (imageGraph jbc_Pce)).ConnectedComponent = 2 := by
  have h1 := jfc_whb_bounded_add_one_eq_card jbc_Pce
  rw [jfc_sq_faithfulRegionCount] at h1
  omega






theorem jcx_square_peel_witness :
    jbc_cyc4 ≤ jbc_Pce.G ∧
    jce_ClosedContour (jei_pushGraph jbc_Pce (⊥ : SimpleGraph (Fin 4))).edgeSet ∧
    (⊥ : SimpleGraph (Fin 4)).edgeSet.ncard < jbc_cyc4.edgeSet.ncard ∧
    faceCount (⊥ : SimpleGraph (Fin 4)) + 1 = faceCount jbc_cyc4 ∧
    Nat.card (whb_faceRegion (jei_pushGraph jbc_Pce jbc_Pce.G)).ConnectedComponent
      = Nat.card (whb_faceRegion (jei_pushGraph jbc_Pce (⊥ : SimpleGraph (Fin 4)))).ConnectedComponent
        + 1 := by
  have hbotV : (⊥ : SimpleGraph (Fin 4)) = (⊥ : SimpleGraph jbc_Pce.V) := rfl
  refine ⟨le_rfl, ?_, ?_, ?_, ?_⟩
  · rw [hbotV, jei_pushGraph_bot jbc_Pce, SimpleGraph.edgeSet_bot]
    have h := jce_empty_closedContour
    rw [Finset.coe_empty] at h
    exact h
  · rw [SimpleGraph.edgeSet_bot, Set.ncard_empty, Set.ncard_pos (Set.toFinite _)]
    exact ⟨s(0, 1), by rw [SimpleGraph.mem_edgeSet, jbc_cyc4_adj]; decide⟩
  · have h2 : faceCount jbc_cyc4 = 2 := whb_square_faceCount
    have h1 : faceCount (⊥ : SimpleGraph (Fin 4)) = 1 := by
      unfold faceCount nullity
      rw [SimpleGraph.edgeSet_bot, Set.ncard_empty, card_components_bot]; simp
    omega
  · rw [jei_pushGraph_G jbc_Pce, hbotV, jei_pushGraph_bot jbc_Pce, jfc_whb_bot,
      jcx_square_dual_card]
    have hlat : Nat.card (hypercubicLattice 2).ConnectedComponent = 1 := by
      have hreach : ∀ a b : Site 2, (hypercubicLattice 2).Reachable a b :=
        fun a b => pbs_reach_all a b
      have hsub : Subsingleton (hypercubicLattice 2).ConnectedComponent :=
        ⟨ConnectedComponent.ind₂ (fun a b => ConnectedComponent.sound (hreach a b))⟩
      haveI : Nonempty (hypercubicLattice 2).ConnectedComponent :=
        ⟨(hypercubicLattice 2).connectedComponentMk ![0, 0]⟩
      rw [Nat.card_eq_one_iff_unique]; exact ⟨hsub, inferInstance⟩
    rw [hlat]


















theorem jcx_pushGraph_degree_corner (P : PlanarZ2Subgraph) (K : SimpleGraph P.V)
    [Fintype P.V] [DecidableRel K.Adj] [SimpleGraph.LocallyFinite (jei_pushGraph P K)]
    [SimpleGraph.LocallyFinite K] (v : P.V) :
    (jei_pushGraph P K).degree (P.emb v) = K.degree v := by
  classical
  rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
  symm
  apply Finset.card_bij (fun w _ => P.emb w)
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset] at hw
    rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj]
    exact ⟨v, w, hw, rfl, rfl⟩
  · intro a _ b _ h; exact P.emb.injective h
  · intro w hw
    rw [SimpleGraph.mem_neighborFinset, jei_pushGraph_adj] at hw
    obtain ⟨x, y, hxy, hx, hy⟩ := hw
    have hxv : x = v := P.emb.injective hx
    subst hxv
    exact ⟨y, by rw [SimpleGraph.mem_neighborFinset]; exact hxy, hy⟩






theorem jcx_square_even_subgraph (K : SimpleGraph (Fin 4)) [DecidableRel K.Adj]
    (hle : K ≤ jbc_cyc4) (heven : ∀ i, Even (Nat.card (K.neighborSet i))) :
    K = ⊥ ∨ K = jbc_cyc4 := by
  have hncard : ∀ i : Fin 4, Nat.card (K.neighborSet i) = K.degree i := fun i =>
    (Nat.card_eq_fintype_card).trans (SimpleGraph.card_neighborSet_eq_degree K i)
  replace heven : ∀ i, Even (K.degree i) := fun i => (hncard i) ▸ heven i
  have hdeg : ∀ i : Fin 4, K.degree i = ∑ j : Fin 4, (if K.Adj i j then 1 else 0) := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, Finset.card_eq_sum_ones]
    rw [SimpleGraph.neighborFinset_eq_filter, Finset.sum_filter]
  have hadj : ∀ i j, K.Adj i j → jbc_cyc4.Adj i j := fun i j h => hle h
  have hn : ∀ i j : Fin 4, jbc_cyc4Rel i j = false → ¬ K.Adj i j := by
    intro i j h hk
    have h2 := hadj i j hk; rw [jbc_cyc4_adj, h] at h2; exact Bool.false_ne_true h2
  have hn02 : ¬ K.Adj 0 2 := hn 0 2 (by decide)
  have hn20 : ¬ K.Adj 2 0 := hn 2 0 (by decide)
  have hn13 : ¬ K.Adj 1 3 := hn 1 3 (by decide)
  have hn31 : ¬ K.Adj 3 1 := hn 3 1 (by decide)
  have hl0 : ¬ K.Adj 0 0 := K.irrefl
  have hl1 : ¬ K.Adj 1 1 := K.irrefl
  have hl2 : ¬ K.Adj 2 2 := K.irrefl
  have hl3 : ¬ K.Adj 3 3 := K.irrefl
  have s10 : K.Adj 1 0 ↔ K.Adj 0 1 := ⟨fun h => h.symm, fun h => h.symm⟩
  have s21 : K.Adj 2 1 ↔ K.Adj 1 2 := ⟨fun h => h.symm, fun h => h.symm⟩
  have s32 : K.Adj 3 2 ↔ K.Adj 2 3 := ⟨fun h => h.symm, fun h => h.symm⟩
  have s30 : K.Adj 3 0 ↔ K.Adj 0 3 := ⟨fun h => h.symm, fun h => h.symm⟩
  have he0 := heven 0; have he1 := heven 1; have he2 := heven 2; have he3 := heven 3
  rw [hdeg, Fin.sum_univ_four] at he0 he1 he2 he3
  simp only [if_neg hl0, if_neg hl1, if_neg hl2, if_neg hl3,
    if_neg hn02, if_neg hn20, if_neg hn13, if_neg hn31,
    s10, s21, s32, s30, Nat.add_zero, Nat.zero_add] at he0 he1 he2 he3
  have eq01_03 : K.Adj 0 1 ↔ K.Adj 0 3 := by
    by_cases a : K.Adj 0 1 <;> by_cases b : K.Adj 0 3 <;>
      simp only [a, b, if_true, if_false] at he0 <;> simp_all
  have eq01_12 : K.Adj 0 1 ↔ K.Adj 1 2 := by
    by_cases a : K.Adj 0 1 <;> by_cases b : K.Adj 1 2 <;>
      simp only [a, b, if_true, if_false] at he1 <;> simp_all
  have eq12_23 : K.Adj 1 2 ↔ K.Adj 2 3 := by
    by_cases a : K.Adj 1 2 <;> by_cases b : K.Adj 2 3 <;>
      simp only [a, b, if_true, if_false] at he2 <;> simp_all
  by_cases c01 : K.Adj 0 1
  · right
    have c12 := eq01_12.mp c01
    have c23 := eq12_23.mp c12
    have c03 := eq01_03.mp c01
    have a01 : K.Adj 0 1 := c01; have a10 : K.Adj 1 0 := c01.symm
    have a12 : K.Adj 1 2 := c12; have a21 : K.Adj 2 1 := c12.symm
    have a23 : K.Adj 2 3 := c23; have a32 : K.Adj 3 2 := c23.symm
    have a03 : K.Adj 0 3 := c03; have a30 : K.Adj 3 0 := c03.symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [] <;> rw [jbc_cyc4_adj, jbc_cyc4Rel] <;>
      first
        | (exact iff_of_true (by assumption) (by decide))
        | (exact iff_of_false (by assumption) (by decide))
  · left
    have c12 : ¬ K.Adj 1 2 := fun h => c01 (eq01_12.mpr h)
    have c23 : ¬ K.Adj 2 3 := fun h => c12 (eq12_23.mpr h)
    have c03 : ¬ K.Adj 0 3 := fun h => c01 (eq01_03.mpr h)
    have n10 : ¬ K.Adj 1 0 := fun h => c01 h.symm
    have n21 : ¬ K.Adj 2 1 := fun h => c12 h.symm
    have n32 : ¬ K.Adj 3 2 := fun h => c23 h.symm
    have n30 : ¬ K.Adj 3 0 := fun h => c03 h.symm
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [] <;> rw [SimpleGraph.bot_adj, iff_false] <;>
      (intro h; exact absurd h (by assumption))








theorem jcx_evenPeel_unitSquare : jcx_EvenPeel jbc_Pce := by
  classical
  intro K hKle hcc hKne
  classical
  
  haveI : Fintype jbc_Pce.V := inferInstanceAs (Fintype (Fin 4))
  haveI hdec : DecidableRel K.Adj := Classical.decRel _
  haveI hlf : SimpleGraph.LocallyFinite (jei_pushGraph jbc_Pce K) :=
    jfc_pushGraph_locallyFinite jbc_Pce K hKle
  have hsub : jei_pushGraph jbc_Pce K ≤ hypercubicLattice 2 :=
    jfc_pushGraph_le_lattice jbc_Pce K hKle
  
  have hncard : ∀ i : Fin 4, Nat.card (K.neighborSet i) = K.degree i := fun i =>
    (Nat.card_eq_fintype_card).trans (SimpleGraph.card_neighborSet_eq_degree K i)
  have heven : ∀ i : Fin 4, Even (Nat.card (K.neighborSet i)) := by
    intro i
    have hcorner := hcc (jbc_csq i)
    rw [jeb_jce_degree_eq_degree (jei_pushGraph jbc_Pce K) hsub (jbc_csq i)] at hcorner
    have hdt : (jei_pushGraph jbc_Pce K).degree ((jbc_Pce.emb) i) = K.degree i :=
      jcx_pushGraph_degree_corner jbc_Pce K i
    have heq : (jei_pushGraph jbc_Pce K).degree (jbc_csq i) = K.degree i := hdt
    rw [heq, ← hncard i] at hcorner
    exact hcorner
  rcases jcx_square_even_subgraph (K : SimpleGraph (Fin 4)) hKle heven with hbot | hfull
  · exact absurd hbot hKne
  · 
    subst hfull
    obtain ⟨_, hcc', hlt, hface, hdual⟩ := jcx_square_peel_witness
    exact ⟨⊥, bot_le, hcc', hlt, hface, hdual⟩







theorem jcx_faithfulDiscreteJordan_unitSquare_viaPeel :
    whc_FaithfulDiscreteJordan jbc_Pce :=
  jcx_faithfulDiscreteJordan_of_evenResidue jbc_Pce jeb_square_closedContour
    (jcx_evenCountResidue_of_evenPeel jbc_Pce jcx_evenPeel_unitSquare)

end Lattice

end StatMech
