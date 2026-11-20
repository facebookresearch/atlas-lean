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
import Code.Percolation.ForestLeafCountClose

open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace

namespace StatMech

namespace Percolation

variable {d : ℕ}












abbrev str_SpiderV (N : Type*) := Option (N ⊕ (N × Fin 2))



def str_sAdj {N : Type*} [DecidableEq N] (a b : str_SpiderV N) : Bool :=
  match a, b with
  | none, some (Sum.inl _) => true
  | some (Sum.inl _), none => true
  | some (Sum.inl i), some (Sum.inr p) => decide (i = p.1)
  | some (Sum.inr p), some (Sum.inl i) => decide (i = p.1)
  | _, _ => false


def str_spiderG (N : Type*) [DecidableEq N] : SimpleGraph (str_SpiderV N) :=
  SimpleGraph.fromRel (fun a b => str_sAdj a b = true)

instance {N : Type*} [DecidableEq N] : DecidableRel (str_spiderG N).Adj := by
  unfold str_spiderG fromRel; intro a b; simp only; infer_instance

variable {N : Type*} [Fintype N] [DecidableEq N]

omit [Fintype N] in

theorem str_spider_adj (a b : str_SpiderV N) :
    (str_spiderG N).Adj a b ↔ a ≠ b ∧ (str_sAdj a b = true ∨ str_sAdj b a = true) := by
  rw [str_spiderG, fromRel_adj]

omit [Fintype N] in

theorem str_spider_reach_root (v : str_SpiderV N) : (str_spiderG N).Reachable none v := by
  match v with
  | none => exact Reachable.refl _
  | some (Sum.inl i) =>
      exact Adj.reachable (by rw [str_spider_adj]; exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩)
  | some (Sum.inr p) =>
      have h1 : (str_spiderG N).Adj none (some (Sum.inl p.1)) := by
        rw [str_spider_adj]; exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
      have h2 : (str_spiderG N).Adj (some (Sum.inl p.1)) (some (Sum.inr p)) := by
        rw [str_spider_adj]; exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
      exact (h1.reachable).trans (h2.reachable)

omit [Fintype N] in

theorem str_spiderG_connected : (str_spiderG N).Connected := by
  rw [connected_iff_exists_forall_reachable]; exact ⟨none, fun w => str_spider_reach_root w⟩


theorem str_spider_leaf_deg (p : N × Fin 2) : (str_spiderG N).degree (some (Sum.inr p)) = 1 := by
  rw [← card_neighborFinset_eq_degree]
  have hset : (str_spiderG N).neighborFinset (some (Sum.inr p)) = {some (Sum.inl p.1)} := by
    ext v
    rw [mem_neighborFinset, str_spider_adj]
    constructor
    · rintro ⟨hne, hor⟩
      match v with
      | none => simp [str_sAdj] at hor
      | some (Sum.inl i) =>
          rw [Finset.mem_singleton]
          have hip : i = p.1 := by
            rcases hor with h | h <;> · simp only [str_sAdj] at h; simpa using h
          rw [hip]
      | some (Sum.inr q) => simp [str_sAdj] at hor
    · intro hv; rw [Finset.mem_singleton] at hv; subst hv
      exact ⟨by simp, Or.inr (by simp [str_sAdj])⟩
  rw [hset, Finset.card_singleton]


theorem str_spider_hub_deg (i : N) : (str_spiderG N).degree (some (Sum.inl i)) = 3 := by
  rw [← card_neighborFinset_eq_degree]
  have hset : (str_spiderG N).neighborFinset (some (Sum.inl i))
      = {none, some (Sum.inr (i, 0)), some (Sum.inr (i, 1))} := by
    ext v
    rw [mem_neighborFinset, str_spider_adj]
    constructor
    · rintro ⟨hne, hor⟩
      match v with
      | none => simp
      | some (Sum.inl j) => rcases hor with h | h <;> simp [str_sAdj] at h
      | some (Sum.inr q) =>
          have hiq : i = q.1 := by
            rcases hor with h | h <;> · simp only [str_sAdj] at h; exact (by simpa using h)
          have hv : (Sum.inr q : N ⊕ N × Fin 2) = Sum.inr (i, q.2) := by simp [hiq]
          rw [hv]
          have : q.2 = 0 ∨ q.2 = 1 := by omega
          rcases this with h2 | h2 <;> simp [h2]
    · intro hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl | rfl
      · exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
      · exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
      · exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
  rw [hset, Finset.card_insert_of_notMem (by simp), Finset.card_insert_of_notMem (by simp),
    Finset.card_singleton]


theorem str_spider_root_deg : (str_spiderG N).degree none = Fintype.card N := by
  rw [← card_neighborFinset_eq_degree]
  have hset : (str_spiderG N).neighborFinset (none : str_SpiderV N)
      = (univ : Finset N).image (fun i => some (Sum.inl i)) := by
    ext v
    rw [mem_neighborFinset, str_spider_adj, Finset.mem_image]
    constructor
    · rintro ⟨hne, hor⟩
      match v with
      | none => simp at hne
      | some (Sum.inl j) => exact ⟨j, Finset.mem_univ _, rfl⟩
      | some (Sum.inr q) => rcases hor with h | h <;> simp [str_sAdj] at h
    · rintro ⟨i, _, rfl⟩
      exact ⟨by simp, Or.inl (by simp [str_sAdj])⟩
  rw [hset, Finset.card_image_of_injective _ (by intro a b h; simpa using h), Finset.card_univ]


theorem str_spider_sum_deg : ∑ v, (str_spiderG N).degree v = 6 * Fintype.card N := by
  rw [Fintype.sum_option, Fintype.sum_sum_type, str_spider_root_deg]
  simp only [str_spider_hub_deg, str_spider_leaf_deg]
  rw [Finset.sum_const, Finset.sum_const]
  simp only [card_univ, Fintype.card_prod, Fintype.card_fin, smul_eq_mul, mul_one]
  ring

omit [DecidableEq N] in

theorem str_spider_card_V : Fintype.card (str_SpiderV N) = 1 + 3 * Fintype.card N := by
  simp only [str_SpiderV, Fintype.card_option, Fintype.card_sum, Fintype.card_prod,
    Fintype.card_fin]
  ring


theorem str_spider_edge_card : (str_spiderG N).edgeFinset.card = 3 * Fintype.card N := by
  have h := (str_spiderG N).sum_degrees_eq_twice_card_edges
  rw [str_spider_sum_deg] at h; omega


theorem str_spiderG_isTree : (str_spiderG N).IsTree := by
  rw [isTree_iff_connected_and_card]
  refine ⟨str_spiderG_connected, ?_⟩
  have hcard : Nat.card (str_spiderG N).edgeSet = (str_spiderG N).edgeFinset.card := by
    rw [Nat.card_eq_fintype_card, ← Set.toFinset_card]; rfl
  rw [hcard, str_spider_edge_card, Nat.card_eq_fintype_card, str_spider_card_V]; ring

omit [DecidableEq N] in

theorem str_spider_two_le_card (hN : 1 ≤ Fintype.card N) : 2 ≤ Fintype.card (str_SpiderV N) := by
  rw [str_spider_card_V]; omega



theorem str_spider_leaf_cases (v : str_SpiderV N) (hv : (str_spiderG N).degree v = 1) :
    v = none ∨ ∃ p, v = some (Sum.inr p) := by
  match v with
  | none => left; rfl
  | some (Sum.inl i) => rw [str_spider_hub_deg] at hv; omega
  | some (Sum.inr p) => right; exact ⟨p, rfl⟩



















def str_ForestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) : Prop :=
  ∃ (r₀ : Site d) (ℓ : Site d → Fin 2 → Site d),
    r₀ ∈ vertexBoundary d n ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, ℓ x j ∈ vertexBoundary d n) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, Connected d ω x (ℓ x j)) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, ℓ x j ≠ r₀) ∧
    (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ∀ j j', ℓ x j = ℓ y j' → x = y ∧ j = j')









open Classical in





theorem str_spanningTreeLeafCount_of_forestLeafSelection
    (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n)
    (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
    flc2_SpanningTreeLeafCount ω n := by
  classical
  obtain ⟨r₀, ℓ, hr₀, hℓbdry, hℓconn, hℓr₀, hℓinj⟩ := h
  
  by_cases hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x
  · exact hbase hno
  · 
    push Not at hno
    obtain ⟨x₀, hx₀box, hx₀tri⟩ := hno
    
    set T := tfc_trifFinset ω n with hT
    set N := {x : Site d // x ∈ T} with hN
    have hx₀T : x₀ ∈ T := tfc_mem_trifFinset.mpr ⟨hx₀box, hx₀tri⟩
    have hNcard : 1 ≤ Fintype.card N := by
      have : Fintype.card N = T.card := Fintype.card_coe T
      rw [this]; exact Finset.card_pos.mpr ⟨x₀, hx₀T⟩
    
    set ιT : Site d → str_SpiderV N := fun x =>
      if hx : x ∈ T then some (Sum.inl ⟨x, hx⟩) else none with hιT
    
    set lamL : str_SpiderV N → Site d := fun v =>
      match v with
      | none => r₀
      | some (Sum.inl _) => r₀
      | some (Sum.inr (i, j)) => ℓ i.1 j with hlamL
    refine ⟨str_SpiderV N, inferInstance, inferInstance, str_spiderG N, inferInstance,
      ιT, lamL, str_spiderG_isTree, str_spider_two_le_card hNcard, ?_, ?_, ?_, ?_⟩
    · 
      intro x hxbox htri
      have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
      have hιx : ιT x = some (Sum.inl ⟨x, hxT⟩) := by rw [hιT]; simp only [dif_pos hxT]
      rw [hιx, str_spider_hub_deg]
    · 
      intro x hxbox htri y hybox htriy hxy
      have hxT : x ∈ T := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
      have hyT : y ∈ T := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
      have hιx : ιT x = some (Sum.inl ⟨x, hxT⟩) := by rw [hιT]; simp only [dif_pos hxT]
      have hιy : ιT y = some (Sum.inl ⟨y, hyT⟩) := by rw [hιT]; simp only [dif_pos hyT]
      rw [hιx, hιy] at hxy
      simp only [Option.some.injEq, Sum.inl.injEq] at hxy
      exact Subtype.ext_iff.mp hxy
    · 
      intro v hv
      rcases str_spider_leaf_cases v hv with rfl | ⟨⟨i, j⟩, rfl⟩
      · 
        rw [hlamL]; exact hr₀
      · 
        rw [hlamL]
        have hi : i.1 ∈ box d n ∧ IsTrifurcation d ω i.1 := tfc_mem_trifFinset.mp i.2
        exact hℓbdry i.1 hi.1 hi.2 j
    · 
      intro u hu v hv huv
      rw [Finset.mem_coe, Finset.mem_filter] at hu hv
      rcases str_spider_leaf_cases u hu.2 with rfl | ⟨⟨iu, ju⟩, rfl⟩ <;>
        rcases str_spider_leaf_cases v hv.2 with rfl | ⟨⟨iv, jv⟩, rfl⟩
      · rfl
      · 
        rw [hlamL] at huv
        have hiv : iv.1 ∈ box d n ∧ IsTrifurcation d ω iv.1 := tfc_mem_trifFinset.mp iv.2
        exact absurd huv.symm (hℓr₀ iv.1 hiv.1 hiv.2 jv)
      · rw [hlamL] at huv
        have hiu : iu.1 ∈ box d n ∧ IsTrifurcation d ω iu.1 := tfc_mem_trifFinset.mp iu.2
        exact absurd huv (hℓr₀ iu.1 hiu.1 hiu.2 ju)
      · 
        rw [hlamL] at huv
        have hiu : iu.1 ∈ box d n ∧ IsTrifurcation d ω iu.1 := tfc_mem_trifFinset.mp iu.2
        have hiv : iv.1 ∈ box d n ∧ IsTrifurcation d ω iv.1 := tfc_mem_trifFinset.mp iv.2
        obtain ⟨hxy, hjj⟩ := hℓinj iu.1 hiu.1 hiu.2 iv.1 hiv.1 hiv.2 ju jv huv
        have hiu_eq : iu = iv := Subtype.ext hxy
        subst hiu_eq; subst hjj; rfl






open Classical in





theorem str_forestLeafSelection_star (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {r a₀ a₁ r₀ : Site d} (hsingle : ∀ x, x ∈ box d n → IsTrifurcation d ω x → x = r)
    (_hrbox : r ∈ box d n) (_htri_r : IsTrifurcation d ω r)
    (ha₀ : a₀ ∈ vertexBoundary d n) (ha₁ : a₁ ∈ vertexBoundary d n) (hr₀ : r₀ ∈ vertexBoundary d n)
    (hc₀ : Connected d ω r a₀) (hc₁ : Connected d ω r a₁)
    (hdistinct : a₀ ≠ a₁ ∧ a₀ ≠ r₀ ∧ a₁ ≠ r₀) :
    str_ForestLeafSelection ω n := by
  classical
  obtain ⟨h01, h0r, h1r⟩ := hdistinct
  refine ⟨r₀, fun _ j => if j = 0 then a₀ else a₁, hr₀, ?_, ?_, ?_, ?_⟩
  · 
    intro x hxbox htri j; rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with h | h <;>
      simp [h, ha₀, ha₁]
  · 
    intro x hxbox htri j
    rw [hsingle x hxbox htri]
    rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with h | h <;> simp only [h] <;>
      simp [hc₀, hc₁]
  · 
    intro x hxbox htri j
    rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with h | h <;> simp [h, h0r, h1r]
  · 
    intro x hxbox htri y hybox htriy j j' hjj
    have hxr := hsingle x hxbox htri
    have hyr := hsingle y hybox htriy
    refine ⟨hxr.trans hyr.symm, ?_⟩
    
    rcases Fin.exists_fin_two.mp ⟨j, rfl⟩ with hj | hj <;>
      rcases Fin.exists_fin_two.mp ⟨j', rfl⟩ with hj' | hj' <;>
      simp only [hj, hj'] at hjj ⊢ <;>
      first
        | rfl
        | (exfalso; simp only [if_neg (by decide : ¬ (1 : Fin 2) = 0)] at hjj
           exact absurd hjj h01)
        | (exfalso; simp only [if_neg (by decide : ¬ (1 : Fin 2) = 0)] at hjj
           exact absurd hjj.symm h01)













theorem str_forestLeafSelection_of_data (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (r₀ : Site d) (ℓ : Site d → Fin 2 → Site d) (hr₀ : r₀ ∈ vertexBoundary d n)
    (hℓbdry : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, ℓ x j ∈ vertexBoundary d n)
    (hℓconn : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, Connected d ω x (ℓ x j))
    (hℓr₀ : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ j, ℓ x j ≠ r₀)
    (hℓinj : ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
      ∀ j j', ℓ x j = ℓ y j' → x = y ∧ j = j') :
    str_ForestLeafSelection ω n :=
  ⟨r₀, ℓ, hr₀, hℓbdry, hℓconn, hℓr₀, hℓinj⟩











theorem str_base_of_twoBoundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d n) (hz₁ : z₁ ∈ vertexBoundary d n)
    (hzne : z₀ ≠ z₁) (hno : ∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) :
    flc2_SpanningTreeLeafCount ω n :=
  flc2_spanningTreeLeafCount_of_noTrif ω n hz₀ hz₁ hzne hno










theorem str_Tcount_le_boundary_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n)
    (hbase : (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
    Tcount d ω n ≤ boxSV_boundaryCard d n :=
  flc2_Tcount_le_boundary_of_spanningTree ω n
    (str_spanningTreeLeafCount_of_forestLeafSelection ω n h hbase)




theorem str_spanningTree_of_forestLeafSelection
    (hsel : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → str_ForestLeafSelection ω n)
    (hbase : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n) :
    ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → flc2_SpanningTreeLeafCount ω n :=
  fun ω n hn =>
    str_spanningTreeLeafCount_of_forestLeafSelection ω n (hsel ω n hn) (hbase ω n hn)














theorem str_burton_keane_bernoulli_of_forestLeafSelection (hd : 1 ≤ d) (p : ℝ≥0) (hp1 : p ≤ 1)
    (hp0 : 0 < p)
    (hsel : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n → str_ForestLeafSelection ω n)
    (hbase : ∀ (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ), 1 ≤ n →
      (∀ x, x ∈ box d n → ¬ IsTrifurcation d ω x) → flc2_SpanningTreeLeafCount ω n)
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
  flc2_burton_keane_bernoulli_of_spanningTree hd p hp1 hp0
    (str_spanningTree_of_forestLeafSelection hsel hbase) htrif

end Percolation

end StatMech
