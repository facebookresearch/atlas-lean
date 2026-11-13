/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Walls.gc40count

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)



section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]







theorem gc42_pairCount_reindex_union
    (P : Finset ι → Prop) [DecidablePred P] (Q : Finset ι → Finset ι → Prop)
    [∀ a, DecidablePred (Q a)] :
    #((univ : Finset (Finset ι × Finset ι)).filter
        (fun p => p.2 ⊆ univ \ p.1 ∧ P (p.1 ∪ p.2) ∧ Q (p.1 ∪ p.2) p.1))
      = ∑ M ∈ (univ : Finset ι).powerset.filter (fun S => P S),
          #(M.powerset.filter (fun S₁ => Q M S₁)) := by
  rw [Finset.card_eq_sum_card_fiberwise (f := fun p : Finset ι × Finset ι => p.1 ∪ p.2)
    (t := (univ : Finset ι).powerset.filter (fun S => P S))
    (by
      intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      simp only [Finset.coe_filter, Finset.mem_powerset, Set.mem_setOf_eq]
      exact ⟨Finset.subset_univ _, hp.2.1⟩)]
  apply Finset.sum_congr rfl
  intro M hM
  simp only [Finset.mem_filter, Finset.mem_powerset] at hM
  apply Finset.card_bij (fun p _ => p.1)
  · 
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    simp only [Finset.mem_powerset, Finset.mem_filter]
    obtain ⟨⟨hsub, hP, hQ⟩, hf⟩ := hp
    refine ⟨?_, ?_⟩
    · rw [← hf]; exact Finset.subset_union_left
    · rw [hf] at hQ; exact hQ
  · 
    intro p hp q hq h
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨⟨hpsub, _, _⟩, hpf⟩ := hp
    obtain ⟨⟨hqsub, _, _⟩, hqf⟩ := hq
    
    have hp2 : p.2 = M \ p.1 := by
      rw [← hpf]; ext i
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hi
        exact ⟨Or.inr hi, fun hc => (Finset.mem_sdiff.mp (hpsub hi)).2 hc⟩
      · rintro ⟨hor, hni⟩; exact hor.resolve_left hni
    have hq2 : q.2 = M \ q.1 := by
      rw [← hqf]; ext i
      simp only [Finset.mem_sdiff, Finset.mem_union]
      constructor
      · intro hi
        exact ⟨Or.inr hi, fun hc => (Finset.mem_sdiff.mp (hqsub hi)).2 hc⟩
      · rintro ⟨hor, hni⟩; exact hor.resolve_left hni
    exact Prod.ext h (by rw [hp2, hq2, h])
  · 
    intro S₁ hS₁
    simp only [Finset.mem_powerset, Finset.mem_filter] at hS₁
    have hunion : S₁ ∪ (M \ S₁) = M := by
      rw [Finset.union_sdiff_self_eq_union, Finset.union_eq_right.mpr hS₁.1]
    have hmem : (S₁, M \ S₁) ∈ ((univ : Finset (Finset ι × Finset ι)).filter
        (fun p => p.2 ⊆ univ \ p.1 ∧ P (p.1 ∪ p.2) ∧ Q (p.1 ∪ p.2) p.1)).filter
        (fun p => p.1 ∪ p.2 = M) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨⟨?_, ?_, ?_⟩, hunion⟩
      · intro i hi
        rw [Finset.mem_sdiff] at hi
        simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
        exact hi.2
      · rw [hunion]; exact hM.2
      · rw [hunion]; exact hS₁.2
    refine ⟨(S₁, M \ S₁), hmem, rfl⟩





theorem gc42_sd_og_xg {o x g : W} (hox : o ≠ x) (hog : o ≠ g) (hxg : x ≠ g) :
    ({o, g} : Finset W) ∆ ({x, g} : Finset W) = ({o, x} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro (⟨h, hn⟩ | ⟨h, hn⟩) <;> tauto
  · rintro (rfl | rfl)
    · exact Or.inl ⟨Or.inl rfl, not_or.2 ⟨hox, hog⟩⟩
    · exact Or.inr ⟨Or.inl rfl, not_or.2 ⟨fun h => hox h.symm, hxg⟩⟩



theorem gc42_union_sources_ox (ends : ι → Sym2 W) {S₁ S₂ : Finset ι} (hd : S₂ ⊆ univ \ S₁)
    {o x g : W} (hox : o ≠ x) (hog : o ≠ g) (hxg : x ≠ g)
    (h1 : sources ends S₁ = ({o, g} : Finset W)) (h2 : sources ends S₂ = ({x, g} : Finset W)) :
    sources ends (S₁ ∪ S₂) = ({o, x} : Finset W) := by
  have hdisj : Disjoint S₁ S₂ := by
    rw [Finset.disjoint_left]; intro i hi1 hi2
    have := hd hi2; rw [Finset.mem_sdiff] at this; exact this.2 hi1
  have hun : S₁ ∪ S₂ = S₁ ∆ S₂ := by
    rw [Disjoint.symmDiff_eq_sup hdisj]; rfl
  rw [hun, sources_symmDiff, h1, h2, gc42_sd_og_xg hox hog hxg]


theorem gc42_sd_ox_xg {o x g : W} (hox : o ≠ x) (hog : o ≠ g) (hxg : x ≠ g) :
    ({o, x} : Finset W) ∆ ({x, g} : Finset W) = ({o, g} : Finset W) := by
  ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases h1 : z = o <;> by_cases h2 : z = x <;> by_cases h3 : z = g <;>
    subst_vars <;> simp_all






theorem gc42_inner_count_collapse (ends : ι → Sym2 W) (M : Finset ι)
    (hnd : ∀ i ∈ M, ¬ (ends i).IsDiag) {o x g : W}
    (hMsrc : sources ends M = ({o, x} : Finset W)) (hox : o ≠ x) (hog : o ≠ g) (hxg : x ≠ g) :
    #(M.powerset.filter (fun S₁ => sources ends S₁ = ({o, g} : Finset W)))
      = (if connK ends M x g then gc40_E ends M else 0) := by
  have hAog : ({o, x} : Finset W) ∆ ({x, g} : Finset W) = ({o, g} : Finset W) :=
    gc42_sd_ox_xg hox hog hxg
  have sw1 := switching_card ends M hnd ({o, x} : Finset W) hMsrc (u := x) (v := g) hxg
  rw [hAog] at sw1
  rw [sw1]
  have hAox : ({o, x} : Finset W) ∆ ({o, x} : Finset W) = (∅ : Finset W) := by rw [symmDiff_self]; rfl
  have sw2 := switching_card ends M hnd ({o, x} : Finset W) hMsrc (u := o) (v := x) hox
  rw [hAox] at sw2
  have hoconn : connK ends M o x := by
    apply path_exists ends M hnd o x
    · rw [← mem_sources, hMsrc]; simp
    · intro z hz
      rw [← mem_sources, hMsrc] at hz
      simp only [Finset.mem_insert, Finset.mem_singleton] at hz; exact hz
    · exact hox
  rw [if_pos hoconn] at sw2
  rw [gc40_E, ← sw2]













theorem gc42_NR_eq_Mform (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    gc40_NR ends o x y g
      = ∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)),
          (if connK ends M x g then gc40_E ends M else 0) := by
  rw [gc40_NR]
  
  rw [show ((univ : Finset (Finset ι × Finset ι)).filter (fun p : Finset ι × Finset ι =>
        p.2 ⊆ univ \ p.1
          ∧ sources ends p.1 = ({o, g} : Finset W)
          ∧ sources ends p.2 = ({x, g} : Finset W)
          ∧ sources ends ((univ \ p.1) \ p.2) = ({y, g} : Finset W)))
      = ((univ : Finset (Finset ι × Finset ι)).filter (fun p : Finset ι × Finset ι =>
        p.2 ⊆ univ \ p.1
          ∧ sources ends (p.1 ∪ p.2) = ({o, x} : Finset W)
          ∧ (sources ends p.1 = ({o, g} : Finset W)))) from ?_]
  · rw [gc42_pairCount_reindex_union (P := fun S => sources ends S = ({o, x} : Finset W))
      (Q := fun _ S₁ => sources ends S₁ = ({o, g} : Finset W))]
    apply Finset.sum_congr rfl
    intro M hM
    simp only [Finset.mem_filter, Finset.mem_powerset] at hM
    rw [gc42_inner_count_collapse ends M (fun i _ => hnd i) hM.2 hox hog hxg]
  · 
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro ⟨hd, h1, h2, h3⟩
      refine ⟨hd, ?_, h1⟩
      exact gc42_union_sources_ox ends hd hox hog hxg h1 h2
    · rintro ⟨hd, hM, h1⟩
      
      have hdisj : Disjoint p.1 p.2 := by
        rw [Finset.disjoint_left]; intro i hi1 hi2
        have := hd hi2; rw [Finset.mem_sdiff] at this; exact this.2 hi1
      have hun : p.1 ∪ p.2 = p.1 ∆ p.2 := by
        rw [Disjoint.symmDiff_eq_sup hdisj]; rfl
      have h2 : sources ends p.2 = ({x, g} : Finset W) := by
        have := hM
        rw [hun, sources_symmDiff, h1] at this
        
        have hh : sources ends p.2 = ({o, g} : Finset W) ∆ ({o, x} : Finset W) := by
          rw [← this, ← symmDiff_assoc, symmDiff_self, bot_symmDiff]
        rw [hh]
        ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
        by_cases h1' : z = o <;> by_cases h2' : z = x <;> by_cases h3' : z = g <;>
          subst_vars <;> simp_all
      refine ⟨hd, h1, h2, ?_⟩
      
      have hcompl : (univ \ p.1) \ p.2 = univ \ (p.1 ∪ p.2) := by
        ext i; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]; tauto
      rw [hcompl, gc40_sources_compl, huniv, hM]
      ext z; simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
      by_cases h1' : z = o <;> by_cases h2' : z = x <;> by_cases h3' : z = y <;> by_cases h4' : z = g <;>
        subst_vars <;> simp_all





theorem gc42_full_boundary_count_eq_E (ends : ι → Sym2 W) (M : Finset ι) :
    #(M.powerset.filter (fun S => sources ends S = sources ends M)) = gc40_E ends M := by
  rw [gc40_E]
  apply Finset.card_bij (fun S _ => M \ S)
  · 
    intro S hS
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS
    simp only [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.sdiff_subset, ?_⟩
    have hcompl : M \ S = M ∆ S := (symmDiff_of_ge hS.1).symm
    rw [hcompl, sources_symmDiff, hS.2, symmDiff_self]; rfl
  · 
    intro S₁ hS₁ S₂ hS₂ h
    simp only [Finset.mem_filter, Finset.mem_powerset] at hS₁ hS₂
    
    have : M \ (M \ S₁) = M \ (M \ S₂) := by rw [h]
    rwa [Finset.sdiff_sdiff_eq_self hS₁.1, Finset.sdiff_sdiff_eq_self hS₂.1] at this
  · 
    intro T hT
    simp only [Finset.mem_filter, Finset.mem_powerset] at hT
    refine ⟨M \ T, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨Finset.sdiff_subset, ?_⟩
      have hcompl : M \ T = M ∆ T := (symmDiff_of_ge hT.1).symm
      rw [hcompl, sources_symmDiff, hT.2]; exact symmDiff_eq_left.mpr rfl
    · rw [Finset.sdiff_sdiff_eq_self hT.1]










theorem gc42_NL_eq_Mform (ends : ι → Sym2 W) {o x y g : W}
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    gc40_NL ends o x y g
      = ∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)),
          (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0) := by
  rw [gc40_NL]
  
  rw [show ((univ : Finset (Finset ι × Finset ι)).filter (fun p : Finset ι × Finset ι =>
        p.2 ⊆ univ \ p.1
          ∧ sources ends p.1 = ({o, x, y, g} : Finset W)
          ∧ sources ends p.2 = (∅ : Finset W)
          ∧ sources ends ((univ \ p.1) \ p.2) = (∅ : Finset W)
          ∧ connK ends (p.1 ∪ p.2) o x ∧ connK ends (p.1 ∪ p.2) o y ∧ connK ends (p.1 ∪ p.2) o g))
      = ((univ : Finset (Finset ι × Finset ι)).filter (fun p : Finset ι × Finset ι =>
        p.2 ⊆ univ \ p.1
          ∧ (sources ends (p.1 ∪ p.2) = ({o, x, y, g} : Finset W)
              ∧ connK ends (p.1 ∪ p.2) o x ∧ connK ends (p.1 ∪ p.2) o y ∧ connK ends (p.1 ∪ p.2) o g)
          ∧ (sources ends p.1 = ({o, x, y, g} : Finset W)))) from ?_]
  · rw [gc42_pairCount_reindex_union
      (P := fun S => sources ends S = ({o, x, y, g} : Finset W)
          ∧ connK ends S o x ∧ connK ends S o y ∧ connK ends S o g)
      (Q := fun _ S₁ => sources ends S₁ = ({o, x, y, g} : Finset W))]
    
    rw [← Finset.sum_filter (s := (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)))
      (p := fun M => connK ends M o x ∧ connK ends M o y ∧ connK ends M o g)
      (f := fun M => gc40_E ends M)]
    
    rw [Finset.filter_filter]
    apply Finset.sum_congr rfl
    intro M hM
    simp only [Finset.mem_filter, Finset.mem_powerset] at hM
    obtain ⟨_, hMsrc, _⟩ := hM
    rw [← hMsrc, gc42_full_boundary_count_eq_E ends M]
  · 
    apply Finset.filter_congr
    intro p _
    constructor
    · rintro ⟨hd, h1, h2, h3, hcx, hcy, hcg⟩
      
      have hunion : sources ends (p.1 ∪ p.2) = ({o, x, y, g} : Finset W) := by
        have hdisj : Disjoint p.1 p.2 := by
          rw [Finset.disjoint_left]; intro i hi1 hi2
          have := hd hi2; rw [Finset.mem_sdiff] at this; exact this.2 hi1
        have hun : p.1 ∪ p.2 = p.1 ∆ p.2 := by rw [Disjoint.symmDiff_eq_sup hdisj]; rfl
        rw [hun, sources_symmDiff, h1, h2]; exact symmDiff_eq_left.mpr rfl
      exact ⟨hd, ⟨hunion, hcx, hcy, hcg⟩, h1⟩
    · rintro ⟨hd, ⟨hunion, hcx, hcy, hcg⟩, h1⟩
      
      have hdisj : Disjoint p.1 p.2 := by
        rw [Finset.disjoint_left]; intro i hi1 hi2
        have := hd hi2; rw [Finset.mem_sdiff] at this; exact this.2 hi1
      have hun : p.1 ∪ p.2 = p.1 ∆ p.2 := by rw [Disjoint.symmDiff_eq_sup hdisj]; rfl
      have h2 : sources ends p.2 = (∅ : Finset W) := by
        have hthis := hunion
        rw [hun, sources_symmDiff, h1] at hthis
        
        have := symmDiff_eq_left.mp hthis
        exact this
      
      have hcompl : (univ \ p.1) \ p.2 = univ \ (p.1 ∪ p.2) := by
        ext i; simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_univ, true_and]; tauto
      have h3 : sources ends ((univ \ p.1) \ p.2) = (∅ : Finset W) := by
        rw [hcompl, gc40_sources_compl, huniv, hunion, symmDiff_self]; rfl
      exact ⟨hd, h1, h2, h3, hcx, hcy, hcg⟩














def gc42_EMassResidue (ends : ι → Sym2 W) (o x y g : W) : Prop :=
  (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)),
      (if connK ends M x g then gc40_E ends M else 0))
    ≤ ∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)),
        (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0)






theorem gc42_countIneq_of_EMass (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hres : gc42_EMassResidue ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  rw [gc40_countIneq_iff, gc42_NR_eq_Mform ends hnd hox hoy hog hxy hxg hyg huniv,
    gc42_NL_eq_Mform ends huniv]
  exact hres






theorem gc42_NRterm_le_E (ends : ι → Sym2 W) (M : Finset ι) {x g : W} :
    (if connK ends M x g then gc40_E ends M else 0) ≤ gc40_E ends M := by
  by_cases h : connK ends M x g
  · rw [if_pos h]
  · rw [if_neg h]; exact Nat.zero_le _





theorem gc42_NLterm_le_E (ends : ι → Sym2 W) (M : Finset ι) {o x y g : W} :
    (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0)
      ≤ gc40_E ends M := by
  by_cases h : connK ends M o x ∧ connK ends M o y ∧ connK ends M o g
  · rw [if_pos h]
  · rw [if_neg h]; exact Nat.zero_le _





theorem gc42_EMass_iff_countIneq (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    gc42_EMassResidue ends o x y g ↔ gc39_ThreeColouringCountIneq ends o x y g := by
  constructor
  · exact gc42_countIneq_of_EMass ends hnd hox hoy hog hxy hxg hyg huniv
  · intro hcore
    rw [gc40_countIneq_iff, gc42_NR_eq_Mform ends hnd hox hoy hog hxy hxg hyg huniv,
      gc42_NL_eq_Mform ends huniv] at hcore
    exact hcore

end Abstract













theorem gc42_reduction_applies_claw :
    (∀ i : Fin 3, ¬ (gc40_clawEnds i).IsDiag)
      ∧ ((0 : Fin 4) ≠ 1 ∧ (0 : Fin 4) ≠ 2 ∧ (0 : Fin 4) ≠ 3
          ∧ (1 : Fin 4) ≠ 2 ∧ (1 : Fin 4) ≠ 3 ∧ (2 : Fin 4) ≠ 3)
      ∧ sources gc40_clawEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) :=
  ⟨gc40_clawEnds_loopless, ⟨by decide, by decide, by decide, by decide, by decide, by decide⟩,
    gc40_clawEnds_univ_sources⟩





theorem gc42_claw_residue_closes_core
    (hres : gc42_EMassResidue gc40_clawEnds (0 : Fin 4) 1 2 3) :
    gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  gc42_countIneq_of_EMass gc40_clawEnds gc40_clawEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc40_clawEnds_univ_sources hres








theorem gc42_claw_EMassResidue : gc42_EMassResidue gc40_clawEnds (0 : Fin 4) 1 2 3 := by
  unfold gc42_EMassResidue
  
  rw [show ((univ : Finset (Fin 3)).powerset.filter
        (fun S => sources gc40_clawEnds S = ({0, 1} : Finset (Fin 4))))
      = {({0, 1} : Finset (Fin 3))} from by decide]
  rw [show ((univ : Finset (Fin 3)).powerset.filter
        (fun S => sources gc40_clawEnds S = ({0, 1, 2, 3} : Finset (Fin 4))))
      = {({0, 1, 2} : Finset (Fin 3))} from by decide]
  rw [Finset.sum_singleton, Finset.sum_singleton]
  
  have hL : connK gc40_clawEnds ({0, 1} : Finset (Fin 3)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  
  have h01 : connK gc40_clawEnds ({0, 1, 2} : Finset (Fin 3)) (0 : Fin 4) (1 : Fin 4) :=
    Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
  have h02 : connK gc40_clawEnds ({0, 1, 2} : Finset (Fin 3)) (0 : Fin 4) (2 : Fin 4) :=
    Relation.ReflTransGen.head (b := (3 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩
      (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
  have h03 : connK gc40_clawEnds ({0, 1, 2} : Finset (Fin 3)) (0 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩
  rw [if_pos hL, if_pos ⟨h01, h02, h03⟩]
  
  rw [show gc40_E gc40_clawEnds ({0, 1} : Finset (Fin 3)) = 1 from by decide,
    show gc40_E gc40_clawEnds ({0, 1, 2} : Finset (Fin 3)) = 1 from by decide]




theorem gc42_claw_core : gc39_ThreeColouringCountIneq gc40_clawEnds (0 : Fin 4) 1 2 3 :=
  gc42_claw_residue_closes_core gc42_claw_EMassResidue

end StatMech.Walls
