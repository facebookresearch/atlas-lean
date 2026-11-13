/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/















































































import Mathlib
import Code.Walls.bgfacyclicstep
import Code.Walls.bc70globalforest
import Code.Walls.bkwburtonkeane

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
















theorem bgc_adj_of_openAdj_avoiding (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (t a b : Site d)
    (hab : (openSubgraph d ω).Adj a b)
    (hta : a ∉ bc61_boxAround d L t) (htb : b ∉ bc61_boxAround d L t) :
    (bc67_contractedLattice ω L t).Adj a b := by
  rw [bc67_contractedLattice_adj, openSubgraph_adj] at *
  refine ⟨hab.1, ?_⟩
  
  show removeSites (bc61_boxAround d L t) ω s(a, b) = true
  unfold removeSites
  rw [if_neg, hab.2]
  rintro ⟨t', ht'T, ht'e⟩
  rw [Sym2.mem_iff] at ht'e
  rcases ht'e with rfl | rfl
  · exact hta ht'T
  · exact htb ht'T




theorem bgc_reach_of_openAdj_avoiding (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (t a b : Site d)
    (hab : (openSubgraph d ω).Adj a b)
    (hta : a ∉ bc61_boxAround d L t) (htb : b ∉ bc61_boxAround d L t) :
    (bc67_contractedLattice ω L t).Reachable a b :=
  (bgc_adj_of_openAdj_avoiding ω L t a b hab hta htb).reachable



















def bgc_TrifForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) : Prop :=
  ∃ (S : Set (Site d)) (_ : Fintype (↑S : Type)) (_ : Nonempty (↑S : Type))
    (G : SimpleGraph (↑S : Type)) (_ : DecidableRel G.Adj) (ιU : Site d → (↑S : Type)),
    
    (∀ t a b : (↑S : Type), G.Adj t a → G.Adj t b → a ≠ b →
      ¬ (bc67_contractedLattice ω L (t : Site d)).Reachable (a : Site d) (b : Site d)) ∧
    
    (∀ t a b : (↑S : Type), G.Adj a b → t ≠ a → t ≠ b →
      (bc67_contractedLattice ω L (t : Site d)).Reachable (a : Site d) (b : Site d)) ∧
    
    (∀ v, 1 ≤ G.degree v) ∧
    
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → 3 ≤ G.degree (ιU y)) ∧
    
    (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → ∀ z, z ∈ box d R →
      bc67_IsGnTrifurcation ω L z → ιU y = ιU z → y = z) ∧
    
    (∀ v : (↑S : Type), G.degree v = 1 → (v : Site d) ∈ vertexBoundary d R)








theorem bgc_globalForest_of_trifForestData (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bgc_TrifForestData ω L R) : bc69_Gn_globalForest ω L R := by
  obtain ⟨S, hSfin, hSne, G, hGdec, ιU, Hcut, Hlift, hmin, hdeg3, hιinj, hbdry⟩ := h
  refine ⟨S, hSfin, hSne, G, hGdec, ιU, ?_, hmin, hdeg3, hιinj, hbdry⟩
  exact bgf_bc67_acyclic ω L G (fun v => (v : Site d)) Hcut Hlift


theorem bgc_coarseTcount_of_trifForest (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    (h : bgc_TrifForestData ω L R) :
    bc61_coarseTcount ω L R ≤ boxSV_boundaryCard d R :=
  bc69_coarseTcount_le_boundary ω L R (bgc_globalForest_of_trifForestData ω L R h)



theorem bgc_bc69_of_trifForest (L R : ℕ)
    (hdata : ∀ ω : ConfigSpace (Sym2 (Site d)), bgc_TrifForestData ω L R) :
    ∀ ω : ConfigSpace (Sym2 (Site d)), bc69_Gn_globalForest ω L R :=
  fun ω => bgc_globalForest_of_trifForestData ω L R (hdata ω)















theorem bgc_bk_uniqueness_of_trifForest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) :
    (bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 0} = 1 ∨
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
        {ω | numInfiniteClusters 2 ω = 1} = 1)
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0
      ∧ bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
          {ω | numInfiniteClusters 2 ω ≤ 1} = 1 :=
  bkw_bk_uniqueness_of_forest p hp1 hp0
    (fun ω L R => bgc_globalForest_of_trifForestData ω L R (hdata ω L R))


theorem bgc_top_null_of_trifForest (p : ℝ≥0) (hp1 : p ≤ 1) (hp0 : 0 < p)
    (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) :
    bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1
      {ω | numInfiniteClusters 2 ω = ⊤} = 0 :=
  bkw_top_null_of_forest p hp1 hp0
    (fun ω L R => bgc_globalForest_of_trifForestData ω L R (hdata ω L R))



open Classical in







theorem bgc_trifForestData_of_noTrif (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {z₀ z₁ : Site d} (hz₀ : z₀ ∈ vertexBoundary d R) (hz₁ : z₁ ∈ vertexBoundary d R) (hzne : z₀ ≠ z₁)
    (hno : ∀ y, y ∈ box d R → ¬ bc67_IsGnTrifurcation ω L y) :
    bgc_TrifForestData ω L R := by
  classical
  set S : Set (Site d) := {z₀, z₁} with hS
  have hz₀S : z₀ ∈ S := by rw [hS]; left; rfl
  have hz₁S : z₁ ∈ S := by rw [hS]; right; rfl
  haveI hSfin : Fintype (↑S : Type) := (Set.toFinite S).fintype
  set a : (↑S : Type) := ⟨z₀, hz₀S⟩ with ha
  set b : (↑S : Type) := ⟨z₁, hz₁S⟩ with hb
  have hab : a ≠ b := fun h => hzne (congrArg Subtype.val h)
  let G : SimpleGraph (↑S : Type) := SimpleGraph.fromEdgeSet {s(a, b)}
  haveI hGdec : DecidableRel G.Adj := Classical.decRel _
  
  have hVall : ∀ v : (↑S : Type), v = a ∨ v = b := by
    intro v
    obtain ⟨x, hx⟩ := v
    rw [hS, Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · left; rfl
    · right; rfl
  have hda : G.degree a = 1 := bc69_single_edge_degree a b hab
  have hdb : G.degree b = 1 := bc69_single_edge_degree_b a b hab
  
  have hGadj : ∀ u v : (↑S : Type), G.Adj u v ↔ (u = a ∧ v = b) ∨ (u = b ∧ v = a) := by
    intro u v
    show (SimpleGraph.fromEdgeSet {s(a, b)}).Adj u v ↔ _
    rw [SimpleGraph.fromEdgeSet_adj]
    simp only [Set.mem_singleton_iff, Sym2.eq_iff]
    constructor
    · rintro ⟨(⟨rfl, rfl⟩ | ⟨rfl, rfl⟩), hne⟩
      · left; exact ⟨rfl, rfl⟩
      · right; exact ⟨rfl, rfl⟩
    · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
      · exact ⟨Or.inl ⟨rfl, rfl⟩, hab⟩
      · exact ⟨Or.inr ⟨rfl, rfl⟩, hab.symm⟩
  refine ⟨S, hSfin, ⟨a⟩, G, hGdec, (fun _ => a), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro t x y hx hy hxy _
    apply hxy
    
    rcases hVall t with rfl | rfl
    · 
      have hxb : x = b := ((hGadj a x).mp hx).elim (fun h => h.2) (fun h => absurd h.1 hab)
      have hyb : y = b := ((hGadj a y).mp hy).elim (fun h => h.2) (fun h => absurd h.1 hab)
      rw [hxb, hyb]
    · 
      have hxa : x = a := ((hGadj b x).mp hx).elim (fun h => absurd h.1 hab.symm) (fun h => h.2)
      have hya : y = a := ((hGadj b y).mp hy).elim (fun h => absurd h.1 hab.symm) (fun h => h.2)
      rw [hxa, hya]
  · 
    intro t x y hxy htx hty
    exfalso
    
    rcases (hGadj x y).mp hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
      rcases hVall t with rfl | rfl
    · exact htx rfl
    · exact hty rfl
    · exact hty rfl
    · exact htx rfl
  · 
    intro v; rcases hVall v with rfl | rfl
    · rw [hda]
    · rw [hdb]
  · 
    intro y hy htri; exact absurd htri (hno y hy)
  · 
    intro y hy htri _ _ _ _; exact absurd htri (hno y hy)
  · 
    intro v _; rcases hVall v with rfl | rfl
    · exact hz₀
    · exact hz₁

open Classical in











theorem bgc_trifForestData_of_singleStar (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ)
    {x : Site d} (a : Fin 3 → Site d)
    (hxbox : x ∈ box d R)
    (hxtri : bc67_IsGnTrifurcation ω L x)
    (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
    (habdry : ∀ i, a i ∈ vertexBoundary d R)
    (hxne : ∀ i, a i ≠ x)
    (hainj : Function.Injective a)
    
    (hsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j))
    
    (hroute : ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) :
    bgc_TrifForestData ω L R := by
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
  haveI hSfin : Fintype (↑S : Type) := by rw [hSdef]; exact Set.fintypeRange lab
  set e : Fin 4 ≃ (↑S : Type) :=
    Equiv.ofBijective (fun i => (⟨lab i, hmem i⟩ : (↑S : Type)))
      ⟨fun u v huv => hlabinj (Subtype.ext_iff.mp huv),
        fun ⟨y, hy⟩ => by obtain ⟨i, rfl⟩ := hy; exact ⟨i, rfl⟩⟩ with he
  have heval : ∀ i, (e i : Site d) = lab i := fun i => rfl
  have hsurj : ∀ w : (↑S : Type), ∃ i : Fin 4, e i = w := fun w => e.surjective w
  
  let G : SimpleGraph (↑S : Type) := bc70_star4.map e.toEmbedding
  let hisoG : bc70_star4 ≃g G := SimpleGraph.Iso.map e bc70_star4
  have hisoApp : ∀ i : Fin 4, hisoG i = e i := fun i => SimpleGraph.Iso.map_apply e bc70_star4 i
  have hGadj : ∀ u v : Fin 4, G.Adj (e u) (e v) ↔ bc70_star4.Adj u v := by
    intro u v; have := hisoG.map_adj_iff (v := u) (w := v); simpa [hisoApp] using this
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
  
  have hstar_adj : ∀ u v : Fin 4, bc70_star4.Adj u v ↔
      (u = 0 ∧ v ≠ 0) ∨ (u ≠ 0 ∧ v = 0) := by
    intro u v; fin_cases u <;> fin_cases v <;>
      simp only [bc70_star4, SimpleGraph.fromEdgeSet_adj] <;> decide
  refine ⟨S, hSfin, ⟨e 0⟩, G, hGdec, (fun _ => e 0), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · 
    intro t p q htp htq hpq
    obtain ⟨it, rfl⟩ := hsurj t
    obtain ⟨ip, rfl⟩ := hsurj p
    obtain ⟨iq, rfl⟩ := hsurj q
    rw [hGadj] at htp htq
    
    have hit0 : it = 0 := by
      rcases (hstar_adj it ip).mp htp with ⟨h, _⟩ | ⟨_, hip0⟩
      · exact h
      · rcases (hstar_adj it iq).mp htq with ⟨h, _⟩ | ⟨_, hiq0⟩
        · exact h
        · exact absurd (hip0.trans hiq0.symm) (fun h => hpq (by rw [h]))
    subst hit0
    have hip0 : ip ≠ 0 := ((hstar_adj 0 ip).mp htp).elim (fun h => h.2) (fun h => absurd h.1 (by decide))
    have hiq0 : iq ≠ 0 := ((hstar_adj 0 iq).mp htq).elim (fun h => h.2) (fun h => absurd h.1 (by decide))
    
    
    have harm : ∀ k : Fin 4, k ≠ 0 → ∃ m : Fin 3, (e k : Site d) = a m := by
      intro k hk; fin_cases k
      · exact absurd rfl hk
      · exact ⟨0, by rw [heval]⟩
      · exact ⟨1, by rw [heval]⟩
      · exact ⟨2, by rw [heval]⟩
    obtain ⟨mp, hmp⟩ := harm ip hip0
    obtain ⟨mq, hmq⟩ := harm iq hiq0
    have hmne : mp ≠ mq := by
      intro h
      apply hpq
      apply Subtype.ext
      rw [hmp, hmq, h]
    
    have he0x : (e 0 : Site d) = x := by rw [heval]
    rw [show ((e (0 : Fin 4) : Site d)) = x from he0x, hmp, hmq]
    exact hsep mp mq hmne
  · 
    intro t p q hpq htp htq
    obtain ⟨it, rfl⟩ := hsurj t
    obtain ⟨ip, rfl⟩ := hsurj p
    obtain ⟨iq, rfl⟩ := hsurj q
    rw [hGadj] at hpq
    
    have he0x : (e 0 : Site d) = x := by rw [heval]
    have harm : ∀ k : Fin 4, k ≠ 0 → ∃ m : Fin 3, (e k : Site d) = a m := by
      intro k hk; fin_cases k
      · exact absurd rfl hk
      · exact ⟨0, by rw [heval]⟩
      · exact ⟨1, by rw [heval]⟩
      · exact ⟨2, by rw [heval]⟩
    
    have hitp : it ≠ ip := fun h => htp (by rw [h])
    have hitq : it ≠ iq := fun h => htq (by rw [h])
    rcases (hstar_adj ip iq).mp hpq with ⟨hip0, hiq0⟩ | ⟨hip0, hiq0⟩
    · 
      subst hip0
      obtain ⟨miq, hmiq⟩ := harm iq hiq0
      have hit0 : it ≠ 0 := hitp
      obtain ⟨mit, hmit⟩ := harm it hit0
      have hmne : miq ≠ mit := by
        intro h; apply htq; apply Subtype.ext; rw [hmit, hmiq, h]
      
      rw [show ((e (0 : Fin 4) : Site d)) = x from he0x, hmiq, hmit]
      exact hroute miq mit hmne
    · 
      subst hiq0
      obtain ⟨mip, hmip⟩ := harm ip hip0
      have hit0 : it ≠ 0 := hitq
      obtain ⟨mit, hmit⟩ := harm it hit0
      have hmne : mip ≠ mit := by
        intro h; apply htp; apply Subtype.ext; rw [hmit, hmip, h]
      rw [show ((e (0 : Fin 4) : Site d)) = x from he0x, hmip, hmit]
      exact (hroute mip mit hmne).symm
  · 
    intro v; obtain ⟨i, rfl⟩ := hsurj v; rw [hdeg]; exact bc70_star4_deg_pos i
  · 
    intro y hybox htri
    have hyx : y = x := hsingle y hybox htri
    
    show 3 ≤ G.degree (e 0)
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
































theorem bgc_status :
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ),
      bgc_TrifForestData ω L R → bc69_Gn_globalForest ω L R) ∧
    
    (∀ (p : ℝ≥0) (hp1 : p ≤ 1), 0 < p →
      (∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) →
      bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0) ∧
    
    (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (t a b : Site d),
      (openSubgraph d ω).Adj a b → a ∉ bc61_boxAround d L t → b ∉ bc61_boxAround d L t →
      (bc67_contractedLattice ω L t).Reachable a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro ω L R h; exact bgc_globalForest_of_trifForestData ω L R h
  · intro p hp1 hp0 hdata; exact (bgc_bk_uniqueness_of_trifForest p hp1 hp0 hdata).2.1
  · intro ω L t a b hab hta htb; exact bgc_reach_of_openAdj_avoiding ω L t a b hab hta htb

end StatMech.Walls
