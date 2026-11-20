/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Walls.gc49nullity2

open Finset BigOperators SimpleGraph
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  switching_card₂ connK_symm exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]




theorem gc50_sd_ox_ox {o x : W} : ({o, x} : Finset W) ∆ ({o, x} : Finset W) = (∅ : Finset W) := by
  rw [symmDiff_self]; rfl



theorem gc50_sd_oxyg_yg {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) :
    ({o, x, y, g} : Finset W) ∆ ({y, g} : Finset W) = ({o, x} : Finset W) :=
  gc49_sd_oxyg_yg hoy hog hxy hxg







theorem gc50_E_eq_oxCount_of_ox_conn (ends : ι → Sym2 W) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) {o x : W} (hox : o ≠ x)
    (hm : sources ends m = ({o, x} : Finset W)) :
    gc40_E ends m = #(m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))) := by
  have hsw := switching_card ends m hnd ({o, x} : Finset W) hm (u := o) (v := x) hox
  rw [gc50_sd_ox_ox] at hsw
  have hoxconn : connK ends m o x := by
    apply path_exists ends m hnd o x
    · rw [← mem_sources, hm]; simp
    · intro z hz
      rw [← mem_sources, hm] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz; exact hz
    · exact hox
  rw [if_pos hoxconn] at hsw
  rw [gc40_E, hsw]



theorem gc50_sd_empty_og_xg {o x g : W} (hox : o ≠ x) (hog : o ≠ g) (hxg : x ≠ g) :
    ((∅ : Finset W) ∆ ({o, g} : Finset W)) ∆ ({x, g} : Finset W) = ({o, x} : Finset W) := by
  rw [show (∅ : Finset W) = (⊥ : Finset W) from rfl, bot_symmDiff]
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inl rfl, not_or.2 ⟨hox, hog⟩⟩
    · exact Or.inr ⟨Or.inl rfl, not_or.2 ⟨fun h => hox h.symm, hxg⟩⟩









theorem gc50_E_eq_oxCount_of_all_conn (ends : ι → Sym2 W) (m : Finset ι)
    {o x g : W} (hox : o ≠ x) (hog : o ≠ g) (hxg : x ≠ g)
    (hconn_ox : connK ends m o x) (hconn_og : connK ends m o g) :
    gc40_E ends m = #(m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))) := by
  
  have hconn_xg : connK ends m x g :=
    Relation.ReflTransGen.trans
      (StatMech.Sharpness.RandomCurrent.connK_symm ends m hconn_ox) hconn_og
  have hsw := switching_card₂ ends m (∅ : Finset W)
    (u := o) (v := g) (s := x) (t := g) hog hxg hconn_og hconn_xg
  rw [gc50_sd_empty_og_xg hox hog hxg] at hsw
  rw [gc40_E, hsw]


















theorem gc50_reindex_by_oxCurrent (ends : ι → Sym2 W) (o x : W) (B Bmox : Finset W)
    (hBmox : B ∆ ({o, x} : Finset W) = Bmox)
    (G : Finset ι → Prop) [DecidablePred G] :
    #(((univ : Finset ι).powerset.filter (fun m => sources ends m = B ∧ G m)).sigma
        (fun m => m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))))
      = ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
          #((univ \ K).powerset.filter (fun R => sources ends R = Bmox ∧ G (K ∪ R))) := by
  rw [Finset.card_sigma]
  
  
  rw [show (∑ m ∈ (univ : Finset ι).powerset.filter (fun m => sources ends m = B ∧ G m),
          #(m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W))))
      = #((univ : Finset (Finset ι × Finset ι)).filter
          (fun p => p.2 ⊆ p.1 ∧ sources ends p.1 = B ∧ G p.1
            ∧ sources ends p.2 = ({o, x} : Finset W))) from ?_]
  · 
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p.2)
      (t := (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)))
      (by
        intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq]
        exact ⟨Finset.subset_univ _, hp.2.2.2⟩)]
    apply Finset.sum_congr rfl
    intro K hK
    simp only [Finset.mem_filter, Finset.mem_powerset] at hK
    
    apply Finset.card_bij (fun p _ => p.1 \ K)
    · 
      intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨hKsub, hmB, hGm, hKsrc⟩, hp2⟩ := hp
      subst hp2
      simp only [Finset.mem_powerset, Finset.mem_filter]
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        rw [Finset.mem_sdiff] at hi
        exact Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hi.2⟩
      · 
        have hcompl : p.1 \ p.2 = p.1 ∆ p.2 := (symmDiff_of_ge hKsub).symm
        rw [hcompl, sources_symmDiff, hmB, hKsrc, hBmox]
      · 
        rw [Finset.union_sdiff_of_subset hKsub]; exact hGm
    · 
      intro a ha b hb hab
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
      obtain ⟨⟨hKa, _, _, _⟩, ha2⟩ := ha
      obtain ⟨⟨hKb, _, _, _⟩, hb2⟩ := hb
      
      have ha1 : a.1 = a.2 ∪ (a.1 \ a.2) := (Finset.union_sdiff_of_subset hKa).symm
      have hb1 : b.1 = b.2 ∪ (b.1 \ b.2) := (Finset.union_sdiff_of_subset hKb).symm
      apply Prod.ext
      · rw [ha1, hb1, ha2, hb2, hab]
      · rw [ha2, hb2]
    · 
      intro R hR
      simp only [Finset.mem_powerset, Finset.mem_filter] at hR
      obtain ⟨hRsub, hRsrc, hGKR⟩ := hR
      refine ⟨(K ∪ R, K), ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        have hdisj : Disjoint K R := by
          rw [Finset.disjoint_left]; intro i hiK hiR
          have := hRsub hiR; rw [Finset.mem_sdiff] at this; exact this.2 hiK
        refine ⟨⟨Finset.subset_union_left, ?_, hGKR, hK.2⟩, trivial⟩
        
        have hun : K ∪ R = K ∆ R := by rw [Disjoint.symmDiff_eq_sup hdisj]; rfl
        rw [hun, sources_symmDiff, hK.2, hRsrc, ← hBmox]
        rw [symmDiff_comm B ({o, x} : Finset W), ← symmDiff_assoc, symmDiff_self, bot_symmDiff]
      · 
        have hdisj : Disjoint K R := by
          rw [Finset.disjoint_left]; intro i hiK hiR
          have := hRsub hiR; rw [Finset.mem_sdiff] at this; exact this.2 hiK
        rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hdisj.symm]
  · 
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p => p.1)
      (t := (univ : Finset ι).powerset.filter (fun m => sources ends m = B ∧ G m))
      (by
        intro p hp
        simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq]
        exact ⟨Finset.subset_univ _, hp.2.1, hp.2.2.1⟩)]
    apply Finset.sum_congr rfl
    intro m hm
    simp only [Finset.mem_filter, Finset.mem_powerset] at hm
    apply Finset.card_bij (fun K _ => (m, K))
    · intro K hK
      simp only [Finset.mem_powerset, Finset.mem_filter] at hK
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨⟨hK.1, hm.2.1, hm.2.2, hK.2⟩, trivial⟩
    · intro a ha b hb hab
      exact congrArg Prod.snd hab
    · intro p hp
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
      obtain ⟨⟨hKsub, _, _, hKsrc⟩, hp1⟩ := hp
      refine ⟨p.2, ?_, ?_⟩
      · simp only [Finset.mem_powerset, Finset.mem_filter]
        exact ⟨hp1 ▸ hKsub, hKsrc⟩
      · exact Prod.ext hp1.symm rfl






noncomputable def gc50_Lblock (ends : ι → Sym2 W) (K : Finset ι) (o x g : W) : ℕ :=
  #((univ \ K).powerset.filter (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ L) x g))




noncomputable def gc50_Rblock (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : ℕ :=
  #((univ \ K).powerset.filter (fun Q => sources ends Q = ({y, g} : Finset W)
      ∧ connK ends (K ∪ Q) o x ∧ connK ends (K ∪ Q) o y ∧ connK ends (K ∪ Q) o g))










theorem gc50_LHS_eq_perKsum (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x g : W}
    (hox : o ≠ x) :
    (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)),
        (if connK ends m x g then gc40_E ends m else 0))
      = ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
          gc50_Lblock ends K o x g := by
  
  have hstep1 :
      (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)),
          (if connK ends m x g then gc40_E ends m else 0))
        = #(((univ : Finset ι).powerset.filter
              (fun m => sources ends m = ({o, x} : Finset W) ∧ connK ends m x g)).sigma
            (fun m => m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W)))) := by
    rw [Finset.card_sigma]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext m; simp only [Finset.mem_filter, Finset.mem_powerset]; tauto
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_powerset] at hm
      rw [gc50_E_eq_oxCount_of_ox_conn ends m (fun i _ => hnd i) hox hm.2.1]
  rw [hstep1]
  
  rw [gc50_reindex_by_oxCurrent ends o x ({o, x} : Finset W) (∅ : Finset W) gc50_sd_ox_ox
    (G := fun m => connK ends m x g)]
  apply Finset.sum_congr rfl
  intro K hK
  rfl



theorem gc50_sd_oxyg_ox {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) :
    ({o, x, y, g} : Finset W) ∆ ({o, x} : Finset W) = ({y, g} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inr (Or.inr (Or.inl rfl)), not_or.2 ⟨fun h => hoy h.symm, fun h => hxy h.symm⟩⟩
    · exact Or.inl ⟨Or.inr (Or.inr (Or.inr rfl)), not_or.2 ⟨fun h => hog h.symm, fun h => hxg h.symm⟩⟩











theorem gc50_RHS_eq_perKsum (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) :
    (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)),
        (if connK ends m o x ∧ connK ends m o y ∧ connK ends m o g then gc40_E ends m else 0))
      = ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
          gc50_Rblock ends K o x y g := by
  
  have hstep1 :
      (∑ m ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)),
          (if connK ends m o x ∧ connK ends m o y ∧ connK ends m o g then gc40_E ends m else 0))
        = #(((univ : Finset ι).powerset.filter
              (fun m => sources ends m = ({o, x, y, g} : Finset W)
                ∧ (connK ends m o x ∧ connK ends m o y ∧ connK ends m o g))).sigma
            (fun m => m.powerset.filter (fun K => sources ends K = ({o, x} : Finset W)))) := by
    rw [Finset.card_sigma]
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext m; simp only [Finset.mem_filter, Finset.mem_powerset]; tauto
    · intro m hm
      simp only [Finset.mem_filter, Finset.mem_powerset] at hm
      rw [gc50_E_eq_oxCount_of_all_conn ends m hox hog hxg hm.2.2.1 hm.2.2.2.2]
  rw [hstep1]
  
  rw [gc50_reindex_by_oxCurrent ends o x ({o, x, y, g} : Finset W) ({y, g} : Finset W)
    (gc50_sd_oxyg_ox hoy hog hxy hxg)
    (G := fun m => connK ends m o x ∧ connK ends m o y ∧ connK ends m o g)]
  apply Finset.sum_congr rfl
  intro K hK
  rfl
























def gc50_PerKDom (ends : ι → Sym2 W) (o x y g : W) : Prop :=
    ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      gc50_Lblock ends K o x g ≤ gc50_Rblock ends K o x y g





theorem gc50_EMassResidue_of_perKDom (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g)
    (h : gc50_PerKDom ends o x y g) :
    gc42_EMassResidue ends o x y g := by
  unfold gc42_EMassResidue
  rw [gc50_LHS_eq_perKsum ends hnd hox, gc50_RHS_eq_perKsum ends hnd hox hoy hog hxy hxg]
  exact Finset.sum_le_sum h








theorem gc50_EMassResidue_iff_perKsum (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) :
    gc42_EMassResidue ends o x y g
      ↔ (∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
            gc50_Lblock ends K o x g)
          ≤ ∑ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
              gc50_Rblock ends K o x y g := by
  unfold gc42_EMassResidue
  rw [gc50_LHS_eq_perKsum ends hnd hox, gc50_RHS_eq_perKsum ends hnd hox hoy hog hxy hxg]




theorem gc50_countIneq_of_perKDom (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : gc50_PerKDom ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc42_countIneq_of_EMass ends hnd hox hoy hog hxy hxg hyg huniv
    (gc50_EMassResidue_of_perKDom ends hnd hox hoy hog hxy hxg h)

end Abstract

open Classical














theorem gc50_witness_oxCurrents :
    (univ : Finset (Fin 4)).powerset.filter
        (fun K => sources gc49_witnessEnds K = ({0, 1} : Finset (Fin 4)))
      = {({1, 3} : Finset (Fin 4)), {2, 3}} := by decide





theorem gc50_witness_Lblock_K13 :
    gc50_Lblock gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 3 = 1 := by
  rw [gc50_Lblock]
  rw [show ((univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4))).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3)
      = {(∅ : Finset (Fin 4))} from ?_]
  · decide
  · 
    have hV : (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
      decide
    rw [hV]
    have hset : ({0, 2} : Finset (Fin 4)).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))
        = {(∅ : Finset (Fin 4))} := by decide
    rw [show ({0, 2} : Finset (Fin 4)).powerset.filter
          (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
            ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3)
        = (({0, 2} : Finset (Fin 4)).powerset.filter
            (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))).filter
              (fun L => connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3) from by
      rw [Finset.filter_filter]]
    rw [hset]
    have hconn : connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) 1 3 := by
      rw [Finset.union_empty]
      exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
    rw [Finset.filter_singleton, if_pos hconn]




theorem gc50_witness_univ_allConn :
    connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 1
      ∧ connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 2
      ∧ connK gc49_witnessEnds (univ : Finset (Fin 4)) 0 3 := by
  refine ⟨?_, ?_, ?_⟩
  · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨1, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩)
  · exact Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
  · exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩




theorem gc50_witness_Rblock_K13 :
    gc50_Rblock gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 = 1 := by
  rw [gc50_Rblock]
  have hV : (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 2} : Finset (Fin 4)).powerset.filter
      (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))
      = {({0, 2} : Finset (Fin 4))} := by decide
  rw [show ({0, 2} : Finset (Fin 4)).powerset.filter
        (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 1
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 2
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 3)
      = (({0, 2} : Finset (Fin 4)).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))).filter
            (fun Q => connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 1
              ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 2
              ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hunivEq : ({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4)) = (univ : Finset (Fin 4)) := by
    decide
  have hconn : connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 1
      ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 2
      ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 3 := by
    rw [hunivEq]; exact gc50_witness_univ_allConn
  rw [Finset.filter_singleton, if_pos hconn, Finset.card_singleton]




theorem gc50_witness_Lblock_K23 :
    gc50_Lblock gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 3 = 1 := by
  rw [gc50_Lblock]
  have hV : (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 1} : Finset (Fin 4)).powerset.filter
      (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))
      = {(∅ : Finset (Fin 4))} := by decide
  rw [show ({0, 1} : Finset (Fin 4)).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ L) 1 3)
      = (({0, 1} : Finset (Fin 4)).powerset.filter
          (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hconn : connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) 1 3 := by
    rw [Finset.union_empty]
    exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos hconn, Finset.card_singleton]




theorem gc50_witness_Rblock_K23 :
    gc50_Rblock gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 = 1 := by
  rw [gc50_Rblock]
  have hV : (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 1} : Finset (Fin 4)).powerset.filter
      (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))
      = {({0, 1} : Finset (Fin 4))} := by decide
  rw [show ({0, 1} : Finset (Fin 4)).powerset.filter
        (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 1
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 2
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 3)
      = (({0, 1} : Finset (Fin 4)).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))).filter
            (fun Q => connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 1
              ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 2
              ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hunivEq : ({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4)) = (univ : Finset (Fin 4)) := by
    decide
  have hconn : connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 1
      ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 2
      ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 3 := by
    rw [hunivEq]; exact gc50_witness_univ_allConn
  rw [Finset.filter_singleton, if_pos hconn, Finset.card_singleton]








theorem gc50_witness_perKDom : gc50_PerKDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · rw [gc50_witness_Lblock_K13, gc50_witness_Rblock_K13]
  · rw [gc50_witness_Lblock_K23, gc50_witness_Rblock_K23]




theorem gc50_witness_EMassResidue_via_perK :
    gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc50_EMassResidue_of_perKDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) gc50_witness_perKDom






theorem gc50_perK_succeeds_where_perN1_fails :
    gc50_PerKDom gc49_witnessEnds (0 : Fin 4) 1 2 3
      ∧ #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
          (fun n₂ => sources gc49_witnessEnds n₂ = ({0, 1} : Finset (Fin 4))
            ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ n₂) 1 3))
        > #(((univ : Finset (Fin 4)) \ ∅).powerset.filter
            (fun m₂ => sources gc49_witnessEnds m₂ = ({0, 1, 2, 3} : Finset (Fin 4))
              ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 1
              ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 2
              ∧ connK gc49_witnessEnds ((∅ : Finset (Fin 4)) ∪ m₂) 0 3)) :=
  ⟨gc50_witness_perKDom, gc49_perN1Dom_false⟩

end StatMech.Walls
