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
import Code.Percolation.BurtonKeaneClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}










theorem flc2_deg_pos_of_connected {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hconn : G.Connected) (hV : 2 ≤ Fintype.card V) (v : V) :
    1 ≤ G.degree v := by
  obtain ⟨w, hw⟩ := Fintype.exists_ne_of_one_lt_card hV v
  have hr : G.Reachable v w := hconn.preconnected v w
  have hex : ∃ u, G.Adj v u := by
    obtain ⟨p⟩ := hr
    cases p with
    | nil => exact absurd rfl (Ne.symm hw)
    | cons hadj _ => exact ⟨_, hadj⟩
  rw [Nat.one_le_iff_ne_zero, ← Nat.pos_iff_ne_zero, G.degree_pos_iff_exists_adj]
  exact hex






theorem flc2_tree_internal_lt_leaves {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hT : G.IsTree) (hV : 2 ≤ Fintype.card V) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      < (univ.filter (fun v => G.degree v = 1)).card := by
  classical
  have hpos := flc2_deg_pos_of_connected G hT.connected hV
  have hhand : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  have hedge : G.edgeFinset.card + 1 = Fintype.card V := hT.card_edgeFinset
  set indI : V → ℤ := fun v => if 3 ≤ G.degree v then 1 else 0 with hindI
  set indL : V → ℤ := fun v => if G.degree v = 1 then 1 else 0 with hindL
  
  have hbound : ∀ v, (2 : ℤ) + indI v - indL v ≤ (G.degree v : ℤ) := by
    intro v
    simp only [hindI, hindL]
    have h1 := hpos v
    have hcast : (1 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h1
    by_cases h3 : 3 ≤ G.degree v
    · have hne1 : ¬ G.degree v = 1 := by omega
      have h3cast : (3 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h3
      simp only [if_pos h3, if_neg hne1]; linarith
    · by_cases h1' : G.degree v = 1
      · have h1cast : (G.degree v : ℤ) = 1 := by exact_mod_cast h1'
        simp only [if_neg h3, if_pos h1']; linarith
      · have h2 : G.degree v = 2 := by omega
        have h2cast : (G.degree v : ℤ) = 2 := by exact_mod_cast h2
        simp only [if_neg h3, if_neg h1']; linarith
  have hsumbound : ∑ v, ((2 : ℤ) + indI v - indL v) ≤ ∑ v, (G.degree v : ℤ) :=
    Finset.sum_le_sum (fun v _ => hbound v)
  
  have hLHS : ∑ v, ((2 : ℤ) + indI v - indL v)
      = 2 * Fintype.card V + (univ.filter (fun v => 3 ≤ G.degree v)).card
        - (univ.filter (fun v => G.degree v = 1)).card := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [hindI, hindL, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_boole, Finset.sum_boole]
    ring
  
  have hRHS : ∑ v, (G.degree v : ℤ) = 2 * Fintype.card V - 2 := by
    have h : (∑ v, (G.degree v : ℤ)) = ((∑ v, G.degree v : ℕ) : ℤ) := by
      rw [Nat.cast_sum]
    rw [h, hhand]; omega
  rw [hLHS, hRHS] at hsumbound
  have hfin : ((univ.filter (fun v => 3 ≤ G.degree v)).card : ℤ)
      < ((univ.filter (fun v => G.degree v = 1)).card : ℤ) := by linarith
  exact_mod_cast hfin









theorem flc2_trifImage_card_le_deg3 {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (Tw : Finset W) (hTw : ∀ w ∈ Tw, 3 ≤ G.degree w) :
    Tw.card ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := by
  classical
  apply Finset.card_le_card
  intro w hw
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact hTw w hw



theorem flc2_leaf_card_le_boundary {W : Type*} [Fintype W] (G : SimpleGraph W)
    [DecidableRel G.Adj] (n : ℕ) (lam : W → Site d)
    (hmap : ∀ v, G.degree v = 1 → lam v ∈ vertexBoundary d n)
    (hinj : Set.InjOn lam (univ.filter (fun v => G.degree v = 1))) :
    (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d n := by
  classical
  rw [← tfc_boundaryFinset_card]
  apply Finset.card_le_card_of_injOn lam
  · intro v hv
    rw [Finset.mem_coe, Finset.mem_filter] at hv
    rw [Finset.mem_coe, tfc_mem_boundaryFinset]
    exact hmap v hv.2
  · exact hinj
























def flc2_SpanningTreeLeafCount (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (W : Type) (_ : Fintype W) (_ : DecidableEq W) (G : SimpleGraph W) (_ : DecidableRel G.Adj)
    (ιT : Site d → W) (lamL : W → Site d),
    G.IsTree ∧ 2 ≤ Fintype.card W ∧
    
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → 3 ≤ G.degree (ιT x)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ιT x = ιT y → x = y) ∧
    
    (∀ v, G.degree v = 1 → lamL v ∈ vertexBoundary d n) ∧
    Set.InjOn lamL (univ.filter (fun v => G.degree v = 1))










theorem flc2_Tcount_le_boundary_of_spanningTree (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : flc2_SpanningTreeLeafCount ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n := by
  classical
  obtain ⟨W, _, _, G, _, ιT, lamL, hTree, hWcard, hdeg3, hιinj, hlammap, hlaminj⟩ := h
  
  set Tf := tfc_trifFinset ω n with hTf
  set Tw : Finset W := Tf.image ιT with hTw
  
  have hιinjOn : Set.InjOn ιT Tf := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, tfc_mem_trifFinset] at hx hy
    exact hιinj x hx.1 hx.2 y hy.1 hy.2 hxy
  have hcardTw : Tw.card = Tf.card := by
    rw [hTw, Finset.card_image_of_injOn hιinjOn]
  
  have hTwdeg : ∀ w ∈ Tw, 3 ≤ G.degree w := by
    intro w hw
    rw [hTw, Finset.mem_image] at hw
    obtain ⟨x, hxT, rfl⟩ := hw
    rw [tfc_mem_trifFinset] at hxT
    exact hdeg3 x hxT.1 hxT.2
  
  have h1 : Tf.card ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := by
    rw [← hcardTw]; exact flc2_trifImage_card_le_deg3 G Tw hTwdeg
  have h2 : (univ.filter (fun v => 3 ≤ G.degree v)).card
      < (univ.filter (fun v => G.degree v = 1)).card :=
    flc2_tree_internal_lt_leaves G hTree hWcard
  have h3 : (univ.filter (fun v => G.degree v = 1)).card ≤ boxSV_boundaryCard d n :=
    flc2_leaf_card_le_boundary G n lamL hlammap hlaminj
  calc Tcount d ω n = Tf.card := (tfc_trifFinset_card ω n).symm
    _ ≤ (univ.filter (fun v => 3 ≤ G.degree v)).card := h1
    _ ≤ (univ.filter (fun v => G.degree v = 1)).card := le_of_lt h2
    _ ≤ boxSV_boundaryCard d n := h3



















theorem flc2_forest_component_card {V : Type*} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hmin : ∀ v, 1 ≤ G.degree v) (v : V) :
    ∃ w, G.Adj v w := by
  rw [← G.degree_pos_iff_exists_adj]; exact hmin v









theorem flc2_forest_internal_le_leaves {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card := by
  classical
  
  have hhand : ∑ v, G.degree v = 2 * G.edgeFinset.card := G.sum_degrees_eq_twice_card_edges
  
  
  have hEle : G.edgeFinset.card + 1 ≤ Fintype.card V := by
    
    obtain ⟨T, hGT, hTmax⟩ := exists_maximal_isAcyclic_of_le_isAcyclic (le_top (a := G)) hacyc
    
    have hmax2 : Maximal IsAcyclic T :=
      ⟨hTmax.1.2, fun H hHac hTH => hTmax.2 ⟨le_top, hHac⟩ hTH⟩
    have hTtree : T.IsTree := isTree_iff_maximal_isAcyclic.mpr ⟨‹Nonempty V›, hmax2⟩
    have hTedge : T.edgeFinset.card + 1 = Fintype.card V := hTtree.card_edgeFinset
    have hsub : G.edgeFinset ⊆ T.edgeFinset := by
      intro e he
      rw [SimpleGraph.mem_edgeFinset] at he ⊢
      exact SimpleGraph.edgeSet_subset_edgeSet.mpr hGT he
    have : G.edgeFinset.card ≤ T.edgeFinset.card := Finset.card_le_card hsub
    omega
  
  set indI : V → ℤ := fun v => if 3 ≤ G.degree v then 1 else 0 with hindI
  set indL : V → ℤ := fun v => if G.degree v = 1 then 1 else 0 with hindL
  have hbound : ∀ v, (2 : ℤ) + indI v - indL v ≤ (G.degree v : ℤ) := by
    intro v
    simp only [hindI, hindL]
    have h1 := hmin v
    have hcast : (1 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h1
    by_cases h3 : 3 ≤ G.degree v
    · have hne1 : ¬ G.degree v = 1 := by omega
      have h3cast : (3 : ℤ) ≤ (G.degree v : ℤ) := by exact_mod_cast h3
      simp only [if_pos h3, if_neg hne1]; linarith
    · by_cases h1' : G.degree v = 1
      · have h1cast : (G.degree v : ℤ) = 1 := by exact_mod_cast h1'
        simp only [if_neg h3, if_pos h1']; linarith
      · have h2 : G.degree v = 2 := by omega
        have h2cast : (G.degree v : ℤ) = 2 := by exact_mod_cast h2
        simp only [if_neg h3, if_neg h1']; linarith
  have hsumbound : ∑ v, ((2 : ℤ) + indI v - indL v) ≤ ∑ v, (G.degree v : ℤ) :=
    Finset.sum_le_sum (fun v _ => hbound v)
  have hLHS : ∑ v, ((2 : ℤ) + indI v - indL v)
      = 2 * Fintype.card V + (univ.filter (fun v => 3 ≤ G.degree v)).card
        - (univ.filter (fun v => G.degree v = 1)).card := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    simp only [hindI, hindL, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [Finset.sum_boole, Finset.sum_boole]
    ring
  
  have hRHS : ∑ v, (G.degree v : ℤ) ≤ 2 * Fintype.card V - 2 := by
    have h : (∑ v, (G.degree v : ℤ)) = ((∑ v, G.degree v : ℕ) : ℤ) := by rw [Nat.cast_sum]
    rw [h, hhand]
    have : (G.edgeFinset.card : ℤ) + 1 ≤ Fintype.card V := by exact_mod_cast hEle
    push_cast
    omega
  rw [hLHS] at hsumbound
  have hfin : ((univ.filter (fun v => 3 ≤ G.degree v)).card : ℤ)
      ≤ ((univ.filter (fun v => G.degree v = 1)).card : ℤ) := by linarith
  exact_mod_cast hfin








namespace Flc2Witness


def pathE (a b : Fin 2) : Prop := (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0)
instance : DecidableRel pathE := fun a b => by unfold pathE; infer_instance

def pathG : SimpleGraph (Fin 2) := SimpleGraph.fromRel pathE
instance : DecidableRel pathG.Adj := by unfold pathG fromRel; intro a b; infer_instance

theorem pathG_isTree : pathG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide

theorem pathG_deg (v : Fin 2) : pathG.degree v = 1 := by fin_cases v <;> decide


def starE (a b : Fin 4) : Prop := (a = 0 ∧ b ≠ 0) ∨ (b = 0 ∧ a ≠ 0)
instance : DecidableRel starE := fun a b => by unfold starE; infer_instance

def starG : SimpleGraph (Fin 4) := SimpleGraph.fromRel starE
instance : DecidableRel starG.Adj := by unfold starG fromRel; intro a b; infer_instance

theorem starG_isTree : starG.IsTree := by
  rw [SimpleGraph.isTree_iff_connected_and_card]
  refine ⟨?_, ?_⟩
  · rw [SimpleGraph.connected_iff_exists_forall_reachable]; exact ⟨0, by decide⟩
  · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide

theorem starG_centre_deg : starG.degree 0 = 3 := by decide
theorem starG_leaf_deg : ∀ v : Fin 4, v ≠ 0 → starG.degree v = 1 := by decide
theorem starG_deg1_iff (v : Fin 4) : starG.degree v = 1 ↔ v ≠ 0 := by
  constructor
  · intro h; rintro rfl; rw [starG_centre_deg] at h; exact absurd h (by decide)
  · exact starG_leaf_deg v

end Flc2Witness








open Classical in




theorem flc2_spanningTreeLeafCount_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d n) (hz₁ : z₁ ∈ vertexBoundary d n)
    (hzne : z₀ ≠ z₁)
    (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    flc2_SpanningTreeLeafCount ω n := by
  classical
  refine ⟨Fin 2, inferInstance, inferInstance, Flc2Witness.pathG, inferInstance,
    (fun _ => (0 : Fin 2)), (fun v => if v = 0 then z₀ else z₁),
    Flc2Witness.pathG_isTree, by decide, ?_, ?_, ?_, ?_⟩
  · 
    intro x hxbox htri; exact absurd htri (hno x hxbox)
  · 
    intro x hxbox htri; exact absurd htri (hno x hxbox)
  · 
    intro v _; fin_cases v
    · simpa using hz₀
    · simpa using hz₁
  · 
    intro u hu v hv huv
    fin_cases u <;> fin_cases v
    · rfl
    · exact absurd huv hzne
    · exact absurd huv.symm hzne
    · rfl

open Classical in





theorem flc2_spanningTreeLeafCount_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {r : Site d} (hrbox : r ∈ box d n) (htri_r : IsTrifurcation d ω r)
    (z : Fin 3 → Site d) (hzb : ∀ i, z i ∈ vertexBoundary d n) (hzinj : Function.Injective z)
    (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r) :
    flc2_SpanningTreeLeafCount ω n := by
  classical
  
  set lamL : Fin 4 → Site d := fun v =>
    if v = 1 then z 0 else if v = 2 then z 1 else if v = 3 then z 2 else z 0 with hlamL
  refine ⟨Fin 4, inferInstance, inferInstance, Flc2Witness.starG, inferInstance,
    (fun _ => (0 : Fin 4)), lamL, Flc2Witness.starG_isTree, by decide, ?_, ?_, ?_, ?_⟩
  · 
    intro x hxbox htri; rw [Flc2Witness.starG_centre_deg]
  · 
    intro x hxbox htri y hybox htriy _
    rw [hsingle x hxbox htri, hsingle y hybox htriy]
  · 
    intro v hv
    rw [Flc2Witness.starG_deg1_iff] at hv
    fin_cases v
    · exact absurd rfl hv
    · simpa [hlamL] using hzb 0
    · simpa [hlamL] using hzb 1
    · simpa [hlamL] using hzb 2
  · 
    intro u hu v hv huv
    rw [Finset.mem_coe, Finset.mem_filter] at hu hv
    rw [Flc2Witness.starG_deg1_iff] at hu hv
    have hu' := hu.2; have hv' := hv.2
    fin_cases u <;> fin_cases v <;>
      first
        | exact absurd rfl hu'
        | exact absurd rfl hv'
        | rfl
        | (revert huv; simp only [hlamL]; intro huv; first
            | (exact absurd (hzinj huv) (by decide))
            | (exact absurd (hzinj huv.symm) (by decide)))













theorem flc2_hbound_of_spanningTree
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → flc2_SpanningTreeLeafCount ω n) :
    ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      Tcount d ω n ≤ boxSV_boundaryCard d n :=
  fun ω n hn => flc2_Tcount_le_boundary_of_spanningTree ω n (hres ω n hn)

















theorem flc2_burton_keane_bernoulli_of_spanningTree (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hres : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      flc2_SpanningTreeLeafCount ω n)
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
  tfc_burton_keane_uniqueness_full (bernoulliProductMeasure (E := Sym2 (Site d)) p hp1)
    (bkc_bernoulli_isErgodic hd p hp1)
    (bkc_bernoulli_hasFiniteEnergyMerge p hp1 hp0)
    (fun n => boxSV_boundaryCard d n)
    (flc2_hbound_of_spanningTree hres)
    (fun n => bkc_boxFinsetBK_card_pos d n)
    (bkc_boundary_vol_tendsto d hd)
    htrif

end Percolation

end StatMech
