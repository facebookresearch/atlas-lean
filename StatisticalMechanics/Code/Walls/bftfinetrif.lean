/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Walls.bcvcutvertex
import Code.Walls.bararmray
import Code.Walls.bfctfinitecount

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}








theorem bft_boxAround_zero (y : Site d) : bc61_boxAround d 0 y = {y} := by
  ext x
  rw [bc61_mem_boxAround, mem_box, Finset.mem_singleton]
  constructor
  · intro h
    funext i
    have hi := h i
    rw [Pi.sub_apply] at hi
    omega
  · intro h; subst h; intro i; simp






theorem bft_contractedLattice_zero (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bc67_contractedLattice ω 0 x = bkg_deleteVertex (openSubgraph d ω) x := by
  apply SimpleGraph.ext
  ext a b
  rw [bc67_contractedLattice_adj, openSubgraph_adj, bkg_deleteVertex_adj, openSubgraph_adj]
  rw [bft_boxAround_zero]
  constructor
  · rintro ⟨hlat, hopen⟩
    unfold removeSites at hopen
    by_cases hx : ∃ t ∈ ({x} : Finset (Site d)), t ∈ s(a, b)
    · rw [if_pos hx] at hopen; exact absurd hopen (by simp)
    · rw [if_neg hx] at hopen
      have hax : a ≠ x := by
        intro h; exact hx ⟨x, Finset.mem_singleton_self x, by rw [Sym2.mem_iff]; left; exact h.symm⟩
      have hbx : b ≠ x := by
        intro h; exact hx ⟨x, Finset.mem_singleton_self x, by rw [Sym2.mem_iff]; right; exact h.symm⟩
      exact ⟨⟨hlat, hopen⟩, hax, hbx⟩
  · rintro ⟨⟨hlat, hopen⟩, hax, hbx⟩
    refine ⟨hlat, ?_⟩
    unfold removeSites
    have hx : ¬ ∃ t ∈ ({x} : Finset (Site d)), t ∈ s(a, b) := by
      rintro ⟨t, ht, htmem⟩
      rw [Finset.mem_singleton] at ht; subst ht
      rw [Sym2.mem_iff] at htmem
      rcases htmem with h | h
      · exact hax h.symm
      · exact hbx h.symm
    rw [if_neg hx]; exact hopen


theorem bft_deleteVertex_le (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bkg_deleteVertex (openSubgraph d ω) x ≤ openSubgraph d ω := by
  intro a b hab; exact hab.1











def bft_FineTrif (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) : Prop :=
  bc67_IsGnTrifurcation ω 0 x


theorem bft_gnIncident_zero (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d) :
    bc67_GnIncident ω 0 x a ↔ (openSubgraph d ω).Adj x a := by
  unfold bc67_GnIncident
  rw [bft_boxAround_zero]
  constructor
  · rintro ⟨b, hb, hadj⟩; rw [Finset.mem_singleton] at hb; subst hb; exact hadj
  · intro h; exact ⟨x, Finset.mem_singleton_self x, h⟩





theorem bft_fineTrif_iff (ω : ConfigSpace (Sym2 (Site d))) (x : Site d) :
    bft_FineTrif ω x ↔
      ∃ a₁ a₂ a₃ : Site d,
        ((openSubgraph d ω).Adj x a₁ ∧ (openSubgraph d ω).Adj x a₂ ∧ (openSubgraph d ω).Adj x a₃) ∧
        ((cluster d (removeSites {x} ω) a₁).Infinite ∧
         (cluster d (removeSites {x} ω) a₂).Infinite ∧
         (cluster d (removeSites {x} ω) a₃).Infinite) ∧
        (¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₁ a₂ ∧
         ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₁ a₃ ∧
         ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₂ a₃) := by
  unfold bft_FineTrif bc67_IsGnTrifurcation
  simp only [bft_gnIncident_zero, bft_boxAround_zero, bft_contractedLattice_zero]





theorem bft_separation (ω : ConfigSpace (Sym2 (Site d))) {x : Site d} (h : bft_FineTrif ω x) :
    ∃ a₁ a₂ a₃ : Site d, a₁ ≠ x ∧ a₂ ≠ x ∧ a₃ ≠ x ∧
      ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₁ a₂ ∧
      ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₁ a₃ ∧
      ¬ (bkg_deleteVertex (openSubgraph d ω) x).Reachable a₂ a₃ := by
  obtain ⟨a₁, a₂, a₃, ⟨ha₁, ha₂, ha₃⟩, _, hsep⟩ := (bft_fineTrif_iff ω x).mp h
  exact ⟨a₁, a₂, a₃, ha₁.ne', ha₂.ne', ha₃.ne', hsep.1, hsep.2.1, hsep.2.2⟩










theorem bft_deg3 (ω : ConfigSpace (Sym2 (Site d))) {S : Finset (Site d)}
    {T : SimpleGraph {v // v ∈ S}} [DecidableRel T.Adj]
    (hTH : T ≤ bfct_restrict (openSubgraph d ω) S) (hTconn : T.Connected)
    {hub : {v // v ∈ S}} (h : bft_FineTrif ω (hub : Site d))
    {a₁ a₂ a₃ : {v // v ∈ S}}
    (he₁ : (a₁ : Site d) ≠ (hub : Site d)) (he₂ : (a₂ : Site d) ≠ (hub : Site d))
    (he₃ : (a₃ : Site d) ≠ (hub : Site d))
    (hs₁₂ : ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₁ : Site d) (a₂ : Site d))
    (hs₁₃ : ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₁ : Site d) (a₃ : Site d))
    (hs₂₃ : ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₂ : Site d) (a₃ : Site d)) :
    3 ≤ T.degree hub := by
  refine bcv_trif_degree_ge_three hTH hTconn
    (fun heq => he₁ (congrArg Subtype.val heq))
    (fun heq => he₂ (congrArg Subtype.val heq))
    (fun heq => he₃ (congrArg Subtype.val heq))
    ?_ ?_ ?_
  · exact bfct_cut_transport (G := openSubgraph d ω) (S := S) hs₁₂
  · exact bfct_cut_transport (G := openSubgraph d ω) (S := S) hs₁₃
  · exact bfct_cut_transport (G := openSubgraph d ω) (S := S) hs₂₃













theorem bft_armRay (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d)
    (hinf : (cluster d (removeSites ({x} : Finset (Site d)) ω) a).Infinite) :
    ∃ r : ℕ → Site d, r 0 = a ∧ Function.Injective r ∧
      (∀ k, (bkg_deleteVertex (openSubgraph d ω) x).Adj (r k) (r (k + 1))) ∧
      (∀ k, (bkg_deleteVertex (openSubgraph d ω) x).Reachable a (r k)) := by
  have hinf' : (cluster d (removeSites (bc61_boxAround d 0 x) ω) a).Infinite := by
    rw [bft_boxAround_zero]; exact hinf
  obtain ⟨r, hr0, hinj, hadj, hreach⟩ := bar_armRay_of_infiniteComponent ω 0 x a hinf'
  refine ⟨r, hr0, hinj, ?_, ?_⟩
  · intro k; rw [← bft_contractedLattice_zero]; exact hadj k
  · intro k; rw [← bft_contractedLattice_zero]; exact hreach k





theorem bft_arm_crosses_boundary (ω : ConfigSpace (Sym2 (Site d))) (x a : Site d) (R : ℕ) (hR : 1 ≤ R)
    (haR : a ∈ box d R)
    (hinf : (cluster d (removeSites ({x} : Finset (Site d)) ω) a).Infinite) :
    ∃ b : Site d, (bkg_deleteVertex (openSubgraph d ω) x).Reachable a b ∧ b ∈ vertexBoundary d R := by
  obtain ⟨r, hr0, hinj, hadj, hreach⟩ := bft_armRay ω x a hinf
  have hlat : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)) := fun k => (hadj k).1.1
  have h0box : r 0 ∈ box d R := by rw [hr0]; exact haR
  obtain ⟨k, hk⟩ := bar_ray_crosses_boundary r hinj hlat R hR h0box
  exact ⟨r k, hreach k, hk⟩



















theorem bft_count (ω : ConfigSpace (Sym2 (Site d))) (S : Finset (Site d))
    {T : SimpleGraph {v // v ∈ S}} [DecidableRel T.Adj]
    (hTH : T ≤ bfct_restrict (openSubgraph d ω) S) (hT : T.IsTree)
    {ι : Type*} [Fintype ι] (f : ι → {v // v ∈ S}) (hf : Function.Injective f)
    (harm : ∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S},
        (a₁ : Site d) ≠ (f i : Site d) ∧ (a₂ : Site d) ≠ (f i : Site d) ∧ (a₃ : Site d) ≠ (f i : Site d) ∧
        ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₁ : Site d) (a₂ : Site d) ∧
        ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₁ : Site d) (a₃ : Site d) ∧
        ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₂ : Site d) (a₃ : Site d))
    (B : Finset {v // v ∈ S}) (hleaf : ∀ v, T.degree v = 1 → v ∈ B) :
    Fintype.card ι ≤ B.card := by
  classical
  refine bfct_count (openSubgraph d ω) S hTH hT f hf ?_ B hleaf
  intro i
  obtain ⟨a₁, a₂, a₃, hn₁, hn₂, hn₃, hs₁₂, hs₁₃, hs₂₃⟩ := harm i
  exact ⟨a₁, a₂, a₃,
    (fun heq => hn₁ (congrArg Subtype.val heq)),
    (fun heq => hn₂ (congrArg Subtype.val heq)),
    (fun heq => hn₃ (congrArg Subtype.val heq)),
    hs₁₂, hs₁₃, hs₂₃⟩





theorem bft_count_hyp_of_fineTrif (ω : ConfigSpace (Sym2 (Site d))) {S : Finset (Site d)}
    {hub : {v // v ∈ S}} (h : bft_FineTrif ω (hub : Site d))
    (hmem : ∀ a₁ a₂ a₃ : Site d,
      ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable a₁ a₂ →
      ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable a₁ a₃ →
      ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable a₂ a₃ →
      a₁ ∈ S ∧ a₂ ∈ S ∧ a₃ ∈ S) :
    ∃ a₁ a₂ a₃ : {v // v ∈ S},
      (a₁ : Site d) ≠ (hub : Site d) ∧ (a₂ : Site d) ≠ (hub : Site d) ∧ (a₃ : Site d) ≠ (hub : Site d) ∧
      ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₁ : Site d) (a₂ : Site d) ∧
      ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₁ : Site d) (a₃ : Site d) ∧
      ¬ (bkg_deleteVertex (openSubgraph d ω) (hub : Site d)).Reachable (a₂ : Site d) (a₃ : Site d) := by
  obtain ⟨a₁, a₂, a₃, hn₁, hn₂, hn₃, hs₁₂, hs₁₃, hs₂₃⟩ := bft_separation ω h
  obtain ⟨hm₁, hm₂, hm₃⟩ := hmem a₁ a₂ a₃ hs₁₂ hs₁₃ hs₂₃
  exact ⟨⟨a₁, hm₁⟩, ⟨a₂, hm₂⟩, ⟨a₃, hm₃⟩, hn₁, hn₂, hn₃, hs₁₂, hs₁₃, hs₂₃⟩

















theorem bft_datum_sep_free (ω : ConfigSpace (Sym2 (Site 2))) (S : Finset (Site 2))
    (ιU : Site 2 → {v // v ∈ S}) (hιU : ∀ y, ((ιU y : {v // v ∈ S}) : Site 2) = y)
    {y : Site 2} (hy : bft_FineTrif ω y)
    (hmem : ∀ a₁ a₂ a₃ : Site 2,
      ¬ (bkg_deleteVertex (openSubgraph 2 ω) y).Reachable a₁ a₂ →
      ¬ (bkg_deleteVertex (openSubgraph 2 ω) y).Reachable a₁ a₃ →
      ¬ (bkg_deleteVertex (openSubgraph 2 ω) y).Reachable a₂ a₃ →
      a₁ ∈ S ∧ a₂ ∈ S ∧ a₃ ∈ S) :
    ∃ v₁ v₂ v₃ : {v // v ∈ S},
      v₁ ≠ ιU y ∧ v₂ ≠ ιU y ∧ v₃ ≠ ιU y ∧
      ¬ (bkg_deleteVertex (bfct_restrict (openSubgraph 2 ω) S) (ιU y)).Reachable v₁ v₂ ∧
      ¬ (bkg_deleteVertex (bfct_restrict (openSubgraph 2 ω) S) (ιU y)).Reachable v₁ v₃ ∧
      ¬ (bkg_deleteVertex (bfct_restrict (openSubgraph 2 ω) S) (ιU y)).Reachable v₂ v₃ := by
  obtain ⟨a₁, a₂, a₃, hn₁, hn₂, hn₃, hs₁₂, hs₁₃, hs₂₃⟩ := bft_separation ω hy
  obtain ⟨hm₁, hm₂, hm₃⟩ := hmem a₁ a₂ a₃ hs₁₂ hs₁₃ hs₂₃
  
  have key : ∀ b c : Site 2,
      ¬ (bkg_deleteVertex (openSubgraph 2 ω) y).Reachable b c →
      ∀ (hb : b ∈ S) (hc : c ∈ S),
      ¬ (bkg_deleteVertex (bfct_restrict (openSubgraph 2 ω) S) (ιU y)).Reachable ⟨b, hb⟩ ⟨c, hc⟩ := by
    intro b c hbc hb hc
    have : ¬ (bkg_deleteVertex (openSubgraph 2 ω) ((ιU y : {v // v ∈ S}) : Site 2)).Reachable
        ((⟨b, hb⟩ : {v // v ∈ S}) : Site 2) ((⟨c, hc⟩ : {v // v ∈ S}) : Site 2) := by
      rw [hιU]; exact hbc
    exact bfct_cut_transport (G := openSubgraph 2 ω) (S := S) this
  refine ⟨⟨a₁, hm₁⟩, ⟨a₂, hm₂⟩, ⟨a₃, hm₃⟩, ?_, ?_, ?_, key a₁ a₂ hs₁₂ hm₁ hm₂,
    key a₁ a₃ hs₁₃ hm₁ hm₃, key a₂ a₃ hs₂₃ hm₂ hm₃⟩
  · intro heq; exact hn₁ (by have := congrArg Subtype.val heq; rw [hιU] at this; exact this)
  · intro heq; exact hn₂ (by have := congrArg Subtype.val heq; rw [hιU] at this; exact this)
  · intro heq; exact hn₃ (by have := congrArg Subtype.val heq; rw [hιU] at this; exact this)







theorem bft_bk (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 :=
  bcv_bk_of_treeData p hp1 hp0 hdata























































theorem bft_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (x : Site d),
      bc67_contractedLattice ω 0 x = bkg_deleteVertex (openSubgraph d ω) x) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (S : Finset (Site d))
      {T : SimpleGraph {v // v ∈ S}} [_i : DecidableRel T.Adj],
      T ≤ bfct_restrict (openSubgraph d ω) S → T.IsTree →
      ∀ {ι : Type} [Fintype ι] (f : ι → {v // v ∈ S}), Function.Injective f →
      (∀ i, ∃ a₁ a₂ a₃ : {v // v ∈ S},
        (a₁ : Site d) ≠ (f i : Site d) ∧ (a₂ : Site d) ≠ (f i : Site d) ∧ (a₃ : Site d) ≠ (f i : Site d) ∧
        ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₁ : Site d) (a₂ : Site d) ∧
        ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₁ : Site d) (a₃ : Site d) ∧
        ¬ (bkg_deleteVertex (openSubgraph d ω) (f i : Site d)).Reachable (a₂ : Site d) (a₃ : Site d)) →
      ∀ (B : Finset {v // v ∈ S}), (∀ v, T.degree v = 1 → v ∈ B) → Fintype.card ι ≤ B.card) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bcv_ClusterTreeData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω x; exact bft_contractedLattice_zero ω x
  · intro ω S T _ hTH hT ι _ f hf harm B hleaf
    exact bft_count ω S hTH hT f hf harm B hleaf
  · intro p hp1 hp0 hdata; exact bft_bk p hp1 hp0 hdata

end StatMech.Walls
