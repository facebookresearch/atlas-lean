/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































import Mathlib
import Code.Walls.bc69count
import Code.Percolation.CanonForestCount

open Set SimpleGraph Finset MeasureTheory Filter Topology
open scoped BigOperators ENNReal NNReal
open StatMech StatMech.Lattice StatMech.ConfigSpace

set_option linter.style.longLine false
set_option linter.unusedDecidableInType false
set_option linter.unusedVariables false
set_option maxRecDepth 4000

namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}







noncomputable def bc70_Gn_clusterGraph (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    SimpleGraph (↑(box d R) : Type) :=
  (openSubgraph d ω).induce (box d R)


theorem bc70_Gn_clusterGraph_adj (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ)
    (a b : (↑(box d R) : Type)) :
    (bc70_Gn_clusterGraph ω R).Adj a b ↔ (openSubgraph d ω).Adj (a : Site d) (b : Site d) :=
  Iff.rfl












noncomputable def bc70_spanningForest (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    SimpleGraph (↑(box d R) : Type) :=
  osf_spanForest (bc70_Gn_clusterGraph ω R)



theorem bc70_spanningForest_acyclic (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    (bc70_spanningForest ω R).IsAcyclic :=
  osf_spanForest_acyclic (bc70_Gn_clusterGraph ω R)


theorem bc70_spanningForest_le (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ) :
    bc70_spanningForest ω R ≤ bc70_Gn_clusterGraph ω R :=
  osf_spanForest_le (bc70_Gn_clusterGraph ω R)





theorem bc70_spanningForest_reachable_of (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ)
    {a b : (↑(box d R) : Type)} (h : (bc70_Gn_clusterGraph ω R).Reachable a b) :
    (bc70_spanningForest ω R).Reachable a b :=
  osf_spanForest_reachable_of (bc70_Gn_clusterGraph ω R) h

open Classical in




theorem bc70_spanningForest_degree_pos (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ)
    {u v : (↑(box d R) : Type)} (hv : v ≠ u)
    (h : (bc70_Gn_clusterGraph ω R).Reachable u v) :
    1 ≤ (bc70_spanningForest ω R).degree u :=
  osf_spanForest_degree_pos_of_reachable_ne (bc70_Gn_clusterGraph ω R) hv h






theorem bc70_spanningForest_leaf_count {V : Type*} [Fintype V] [Nonempty V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (hacyc : G.IsAcyclic) (hmin : ∀ v, 1 ≤ G.degree v) :
    (univ.filter (fun v => 3 ≤ G.degree v)).card
      ≤ (univ.filter (fun v => G.degree v = 1)).card :=
  flc2_forest_internal_le_leaves G hacyc hmin
















def bc70_GnForestStructure (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  bc69_Gn_globalForest ω L R




theorem bc70_globalForest_of_structure (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc70_GnForestStructure ω L R) : bc69_Gn_globalForest ω L R := h




theorem bc70_count_of_globalForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bc69_Gn_globalForest ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc69_coarseTcount_le_boundary ω L R h





theorem bc70_infiniteClusters_top_null_of_globalForest
    (μ : Measure (ConfigSpace (Sym2 (Site d)))) [IsProbabilityMeasure μ] (hd : 1 ≤ d)
    (hinv : IsTranslationInvariant (G := Multiplicative (Site d)) μ)
    (hfe : HasFiniteEnergyMerge μ) (L : ℕ)
    (hStructure : ∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), bc70_GnForestStructure ω L R)
    (hcoarseRoute : 0 < μ {ω | numInfiniteClusters d ω = ⊤} →
      ∃ a₁ a₂ a₃ b₁ b₂ b₃ : Site d,
        0 < μ (bc62_CoarseTrifPrecursor d L a₁ a₂ a₃ b₁ b₂ b₃)) :
    μ {ω | numInfiniteClusters d ω = ⊤} = 0 :=
  bc69_infiniteClusters_top_null_of_globalForest μ hd hinv hfe L
    (fun ω R => bc70_globalForest_of_structure ω L R (hStructure ω R)) hcoarseRoute




theorem bc70_globalForest_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bc69_Gn_globalForest ω L R :=
  bc69_globalForest_of_noTrif ω L R hz₀ hz₁ hzne hno













def bc70_star4 : SimpleGraph (Fin 4) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(0, 2), s(0, 3)}

instance : DecidableRel bc70_star4.Adj := by
  unfold bc70_star4; infer_instance


theorem bc70_star4_deg0 : bc70_star4.degree 0 = 3 := by decide


theorem bc70_star4_deg_leaf : ∀ i : Fin 4, i ≠ 0 → bc70_star4.degree i = 1 := by decide


theorem bc70_star4_deg_pos : ∀ i : Fin 4, 1 ≤ bc70_star4.degree i := by decide


theorem bc70_star4_acyclic : bc70_star4.IsAcyclic := by
  have hTree : bc70_star4.IsTree := by
    rw [SimpleGraph.isTree_iff_connected_and_card]
    refine ⟨?_, ?_⟩
    · rw [SimpleGraph.connected_iff_exists_forall_reachable]
      refine ⟨0, ?_⟩
      intro w; fin_cases w
      · exact Reachable.refl _
      · exact Adj.reachable (by decide)
      · exact Adj.reachable (by decide)
      · exact Adj.reachable (by decide)
    · rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]; decide
  exact hTree.isAcyclic

open Classical in







theorem bc70_globalForest_of_singleStar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hxbox : x ∈ box d R)
    (hxtri : bc67_IsGnTrifurcation ω L x)
    (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
    (habdry : ∀ i, a i ∈ vertexBoundary d R)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a) :
    bc69_Gn_globalForest ω L R := by
  classical
  
  set lab : Fin 4 → Site d := fun v => match v with
    | 0 => x | 1 => a 0 | 2 => a 1 | 3 => a 2 with hlab
  have hlabinj : Function.Injective lab := by
    intro u v huv
    fin_cases u <;> fin_cases v <;> simp only [hlab] at huv <;>
      first
        | rfl
        | (exact absurd huv (hxne 0).symm) | (exact absurd huv (hxne 1).symm)
        | (exact absurd huv (hxne 2).symm) | (exact absurd huv.symm (hxne 0).symm)
        | (exact absurd huv.symm (hxne 1).symm) | (exact absurd huv.symm (hxne 2).symm)
        | (exact absurd (hainj huv) (by decide))
  set S : Set (Site d) := Set.range lab with hSdef
  have hmem : ∀ i : Fin 4, lab i ∈ S := fun i => ⟨i, rfl⟩
  haveI hSfin : Fintype (↑S : Type) := by
    rw [hSdef]; exact Set.fintypeRange lab
  
  set e : Fin 4 ≃ (↑S : Type) :=
    Equiv.ofBijective (fun i => (⟨lab i, hmem i⟩ : (↑S : Type)))
      ⟨fun u v huv => hlabinj (Subtype.ext_iff.mp huv),
        fun ⟨y, hy⟩ => by
          obtain ⟨i, rfl⟩ := hy
          exact ⟨i, rfl⟩⟩ with he
  have heval : ∀ i, (e i : Site d) = lab i := fun i => rfl
  have hsurj : ∀ w : (↑S : Type), ∃ i : Fin 4, e i = w := fun w => e.surjective w
  
  let G : SimpleGraph (↑S : Type) := bc70_star4.map e.toEmbedding
  let hisoG : bc70_star4 ≃g G := SimpleGraph.Iso.map e bc70_star4
  have hisoApp : ∀ i : Fin 4, hisoG i = e i := fun i =>
    SimpleGraph.Iso.map_apply e bc70_star4 i
  have hGadj : ∀ u v : Fin 4, G.Adj (e u) (e v) ↔ bc70_star4.Adj u v := by
    intro u v
    have := hisoG.map_adj_iff (v := u) (w := v)
    simpa [hisoApp] using this
  have hGac : G.IsAcyclic := (hisoG.symm.isAcyclic_iff).mpr bc70_star4_acyclic
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  
  have hdeg : ∀ i : Fin 4, G.degree (e i) = bc70_star4.degree i := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hnbhd : G.neighborFinset (e i) = (bc70_star4.neighborFinset i).image e := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hw
        obtain ⟨j, rfl⟩ := e.surjective w
        exact ⟨j, by rw [SimpleGraph.mem_neighborFinset]; exact (hGadj i j).mp hw, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rw [SimpleGraph.mem_neighborFinset] at hj
        exact (hGadj i j).mpr hj
    rw [hnbhd, Finset.card_image_of_injective _ e.injective]
  
  refine ⟨S, hSfin, ⟨e 0⟩, G, hGdec, (fun _ => e 0), hGac, ?_, ?_, ?_, ?_⟩
  · 
    intro v
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg]; exact bc70_star4_deg_pos i
  · 
    intro y hybox htri
    have hyx : y = x := hsingle y hybox htri
    subst hyx
    rw [hdeg 0, bc70_star4_deg0]
  · 
    intro y hybox htri z hzbox htriz _
    rw [hsingle y hybox htri, hsingle z hzbox htriz]
  · 
    intro v hv
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg] at hv
    rw [heval]
    fin_cases i
    · exact absurd hv (by decide)
    · simp only [hlab]; exact habdry 0
    · simp only [hlab]; exact habdry 1
    · simp only [hlab]; exact habdry 2













theorem bc70_upperLines_arm_ne_zero {R : ℕ} (hR : 1 ≤ R) (i : Fin 3) :
    bc57_pt (R : ℤ) ((i : ℤ) + 1) ≠ (0 : Site 2) := by
  intro h
  have := congrArg (fun p => p 0) h
  simp only [bc57_pt_fst] at this
  simp only [Pi.zero_apply] at this
  omega








theorem bc70_upperLines_globalForest {L R : ℕ} (hL : 3 ≤ L) (hR3 : 4 ≤ R)
    (hsingle : ∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation bc60_upperLines L y → y = 0) :
    bc69_Gn_globalForest bc60_upperLines L R := by
  refine bc70_globalForest_of_singleStar bc60_upperLines L R
    (fun i => bc57_pt (R : ℤ) ((i : ℤ) + 1))
    (bc69_box_zero_mem 2 R)
    (bc67_upperLines_is_G_n_trifurcation hL)
    hsingle ?_ ?_ ?_
  · 
    intro i
    exact bc68_upperLines_boundaryPt (by omega) (by fin_cases i <;> norm_num)
      (by fin_cases i <;> omega)
  · 
    intro i
    exact bc70_upperLines_arm_ne_zero (by omega) i
  · 
    intro i j hij
    have : ((i : ℤ) + 1) = ((j : ℤ) + 1) := by
      have := congrArg (fun p => p 1) hij
      simpa [bc57_pt_snd] using this
    have hijZ : (i : ℤ) = (j : ℤ) := by omega
    exact Fin.ext (by exact_mod_cast hijZ)






theorem bc70_upperLines_count {L R : ℕ} (hL : 3 ≤ L) (hR3 : 4 ≤ R)
    (hsingle : ∀ y, y ∈ box 2 R → bc67_IsGnTrifurcation bc60_upperLines L y → y = 0) :
    bc61_coarseTcount bc60_upperLines L R ≤ boxSV_boundaryCard 2 R :=
  bc70_count_of_globalForest bc60_upperLines L R (bc70_upperLines_globalForest hL hR3 hsingle)












open Classical in







theorem bc70_globalForest_of_doubleStar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {x x' : Site d} (a a' : Fin 3 → Site d)
    (hxtri : bc67_IsGnTrifurcation ω L x) (hx'tri : bc67_IsGnTrifurcation ω L x')
    (hpair : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x ∨ y = x')
    (habdry : ∀ i, a i ∈ vertexBoundary d R) (habdry' : ∀ i, a' i ∈ vertexBoundary d R)
    (lab : Fin 8 → Site d)
    (hlab : lab 0 = x ∧ lab 1 = a 0 ∧ lab 2 = a 1 ∧ lab 3 = a 2 ∧
            lab 4 = x' ∧ lab 5 = a' 0 ∧ lab 6 = a' 1 ∧ lab 7 = a' 2)
    (hlabinj : Function.Injective lab) :
    bc69_Gn_globalForest ω L R := by
  classical
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := hlab
  set S : Set (Site d) := Set.range lab with hSdef
  have hmem : ∀ i : Fin 8, lab i ∈ S := fun i => ⟨i, rfl⟩
  haveI hSfin : Fintype (↑S : Type) := by rw [hSdef]; exact Set.fintypeRange lab
  set e : Fin 8 ≃ (↑S : Type) :=
    Equiv.ofBijective (fun i => (⟨lab i, hmem i⟩ : (↑S : Type)))
      ⟨fun u v huv => hlabinj (Subtype.ext_iff.mp huv),
        fun ⟨y, hy⟩ => by obtain ⟨i, rfl⟩ := hy; exact ⟨i, rfl⟩⟩ with he
  have heval : ∀ i, (e i : Site d) = lab i := fun i => rfl
  have hsurj : ∀ w : (↑S : Type), ∃ i : Fin 8, e i = w := fun w => e.surjective w
  let G : SimpleGraph (↑S : Type) := OsfDoubleStar.dsG.map e.toEmbedding
  let hisoG : OsfDoubleStar.dsG ≃g G := SimpleGraph.Iso.map e OsfDoubleStar.dsG
  have hisoApp : ∀ i : Fin 8, hisoG i = e i := fun i =>
    SimpleGraph.Iso.map_apply e OsfDoubleStar.dsG i
  have hGadj : ∀ u v : Fin 8, G.Adj (e u) (e v) ↔ OsfDoubleStar.dsG.Adj u v := by
    intro u v
    have := hisoG.map_adj_iff (v := u) (w := v)
    simpa [hisoApp] using this
  have hGac : G.IsAcyclic := (hisoG.symm.isAcyclic_iff).mpr OsfDoubleStar.dsG_acyclic
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  have hdeg : ∀ i : Fin 8, G.degree (e i) = OsfDoubleStar.dsG.degree i := by
    intro i
    rw [← SimpleGraph.card_neighborFinset_eq_degree, ← SimpleGraph.card_neighborFinset_eq_degree]
    have hnbhd : G.neighborFinset (e i) = (OsfDoubleStar.dsG.neighborFinset i).image e := by
      ext w
      rw [SimpleGraph.mem_neighborFinset, Finset.mem_image]
      constructor
      · intro hw
        obtain ⟨j, rfl⟩ := e.surjective w
        exact ⟨j, by rw [SimpleGraph.mem_neighborFinset]; exact (hGadj i j).mp hw, rfl⟩
      · rintro ⟨j, hj, rfl⟩
        rw [SimpleGraph.mem_neighborFinset] at hj
        exact (hGadj i j).mpr hj
    rw [hnbhd, Finset.card_image_of_injective _ e.injective]
  
  set ιU : Site d → (↑S : Type) := fun y => if y = x then e 0 else e 4 with hιUdef
  refine ⟨S, hSfin, ⟨e 0⟩, G, hGdec, ιU, hGac, ?_, ?_, ?_, ?_⟩
  · 
    intro v
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg]; exact OsfDoubleStar.dsG_deg_pos i
  · 
    intro y hybox htri
    by_cases hyx : y = x
    · change 3 ≤ G.degree (if y = x then e 0 else e 4)
      rw [if_pos hyx, hdeg 0, OsfDoubleStar.dsG_hub0_deg]
    · 
      rcases hpair y hybox htri with hy | hy
      · exact absurd hy hyx
      · change 3 ≤ G.degree (if y = x then e 0 else e 4)
        rw [if_neg hyx, hdeg 4, OsfDoubleStar.dsG_hub4_deg]
  · 
    intro y hybox htri z hzbox htriz hyz
    
    have hyz' : (if y = x then e 0 else e 4) = (if z = x then e 0 else e 4) := hyz
    by_cases hyx : y = x <;> by_cases hzx : z = x
    · rw [hyx, hzx]
    · rw [if_pos hyx, if_neg hzx] at hyz'
      exact absurd (e.injective hyz') (by decide)
    · rw [if_neg hyx, if_pos hzx] at hyz'
      exact absurd (e.injective hyz') (by decide)
    · 
      rcases hpair y hybox htri with hy | hy
      · exact absurd hy hyx
      · rcases hpair z hzbox htriz with hz | hz
        · exact absurd hz hzx
        · rw [hy, hz]
  · 
    intro v hv
    obtain ⟨i, rfl⟩ := hsurj v
    rw [hdeg] at hv
    rw [heval]
    fin_cases i <;>
      simp only [Fin.isValue, Fin.reduceFinMk, h0, h1, h2, h3, h4, h5, h6, h7] <;>
      first
        | (exact absurd hv (by decide))
        | exact habdry 0 | exact habdry 1 | exact habdry 2
        | exact habdry' 0 | exact habdry' 1 | exact habdry' 2




































theorem bc70_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (R : ℕ), (bc70_spanningForest ω R).IsAcyclic) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x : Site d) (a : Fin 3 → Site d),
      x ∈ box d R → bc67_IsGnTrifurcation ω L x →
      (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x) →
      (∀ i, a i ∈ vertexBoundary d R) → (∀ i, a i ≠ x) → Function.Injective a →
      bc69_Gn_globalForest ω L R) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bc70_GnForestStructure ω L R → bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω R; exact bc70_spanningForest_acyclic ω R
  · intro ω L R x a hxbox hxtri hsingle habdry hxne hainj
    exact bc70_globalForest_of_singleStar ω L R a hxbox hxtri hsingle habdry hxne hainj
  · intro ω L R h
    exact bc70_count_of_globalForest ω L R (bc70_globalForest_of_structure ω L R h)

end StatMech.Walls
