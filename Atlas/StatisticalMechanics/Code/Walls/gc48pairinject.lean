/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Walls.gc47aggregate

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
  exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]

















theorem gc48_pairInjection_of_pairCount_le (ends : ι → Sym2 W) (o x y g : W)
    (hcard : #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g)) :
    gc47_PairInjection ends o x y g := by
  rcases Finset.eq_empty_or_nonempty (gc47_LHSpairs ends o x y g) with hLempty | hLne
  · 
    refine ⟨id, ?_, ?_⟩
    · intro p hp; rw [hLempty] at hp; exact absurd hp (Finset.notMem_empty p)
    · intro a ha; rw [Finset.mem_coe, hLempty] at ha; exact absurd ha (Finset.notMem_empty a)
  · 
    have hRne : (gc47_RHSpairs ends o x y g).Nonempty := by
      rw [← Finset.card_pos]
      exact lt_of_lt_of_le (Finset.card_pos.mpr hLne) hcard
    obtain ⟨r₀, hr₀⟩ := hRne
    
    have hcardcoe : Fintype.card (gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g) := by
      rw [Fintype.card_coe]; exact hcard
    obtain ⟨f, hf⟩ := Function.Embedding.exists_of_card_le_finset hcardcoe
    
    refine ⟨fun p => if h : p ∈ gc47_LHSpairs ends o x y g then f ⟨p, h⟩ else r₀, ?_, ?_⟩
    · 
      intro p hp
      simp only [dif_pos hp]
      exact hf (Set.mem_range_self _)
    · 
      intro a ha b hb hab
      rw [Finset.mem_coe] at ha hb
      simp only [dif_pos ha, dif_pos hb] at hab
      have := f.injective hab
      exact congrArg Subtype.val this




theorem gc48_pairInjection_of_EMassResidue (ends : ι → Sym2 W) (o x y g : W)
    (h : gc42_EMassResidue ends o x y g) :
    gc47_PairInjection ends o x y g :=
  gc48_pairInjection_of_pairCount_le ends o x y g
    ((gc47_EMassResidue_iff_pairCount_le ends o x y g).mp h)









theorem gc48_pairInjection_iff_EMassResidue (ends : ι → Sym2 W) (o x y g : W) :
    gc47_PairInjection ends o x y g ↔ gc42_EMassResidue ends o x y g :=
  ⟨gc47_EMassResidue_of_pairInjection ends o x y g,
    gc48_pairInjection_of_EMassResidue ends o x y g⟩





theorem gc48_pairInjection_iff_pairCount_le (ends : ι → Sym2 W) (o x y g : W) :
    gc47_PairInjection ends o x y g
      ↔ #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g) :=
  (gc48_pairInjection_iff_EMassResidue ends o x y g).trans
    (gc47_EMassResidue_iff_pairCount_le ends o x y g)







noncomputable def gc48_LHSdoubled (ends : ι → Sym2 W) (o x y g : W) :
    Finset (Finset ι × Finset ι) :=
  (univ : Finset (Finset ι × Finset ι)).filter
    (fun p => p.2 ⊆ univ \ p.1
      ∧ sources ends p.1 = (∅ : Finset W)
      ∧ sources ends p.2 = ({o, x} : Finset W)
      ∧ connK ends (p.1 ∪ p.2) x g)



noncomputable def gc48_RHSdoubled (ends : ι → Sym2 W) (o x y g : W) :
    Finset (Finset ι × Finset ι) :=
  (univ : Finset (Finset ι × Finset ι)).filter
    (fun p => p.2 ⊆ univ \ p.1
      ∧ sources ends p.1 = (∅ : Finset W)
      ∧ sources ends p.2 = ({o, x, y, g} : Finset W)
      ∧ connK ends (p.1 ∪ p.2) o x ∧ connK ends (p.1 ∪ p.2) o y ∧ connK ends (p.1 ∪ p.2) o g)








theorem gc48_sigma_card_eq_doubled (ends : ι → Sym2 W) (s : Finset (Finset ι))
    (P : Finset ι → Prop) [DecidablePred P] (hs : ∀ M, M ∈ s ↔ M ⊆ univ ∧ P M) :
    #(s.sigma (fun M => gc45_evenSub ends M))
      = #((univ : Finset (Finset ι × Finset ι)).filter
          (fun p => p.2 ⊆ univ \ p.1 ∧ sources ends p.1 = (∅ : Finset W) ∧ P (p.1 ∪ p.2))) := by
  apply Finset.card_bij (fun q _ => (q.2, q.1 \ q.2))
  · 
    intro q hq
    rw [Finset.mem_sigma] at hq
    obtain ⟨hMs, hSeven⟩ := hq
    rw [gc45_evenSub, Finset.mem_filter, Finset.mem_powerset] at hSeven
    obtain ⟨hSsub, hSsrc⟩ := hSeven
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    have hunion : q.2 ∪ (q.1 \ q.2) = q.1 := by
      rw [Finset.union_sdiff_of_subset hSsub]
    refine ⟨?_, hSsrc, ?_⟩
    · 
      intro i hi
      rw [Finset.mem_sdiff] at hi
      rw [Finset.mem_sdiff]
      exact ⟨Finset.mem_univ _, hi.2⟩
    · rw [hunion]; exact ((hs q.1).mp hMs).2
  · 
    intro a ha b hb hab
    rw [Finset.mem_sigma] at ha hb
    obtain ⟨haMs, haSeven⟩ := ha
    obtain ⟨hbMs, hbSeven⟩ := hb
    rw [gc45_evenSub, Finset.mem_filter, Finset.mem_powerset] at haSeven hbSeven
    have haS : a.2 ⊆ a.1 := haSeven.1
    have hbS : b.2 ⊆ b.1 := hbSeven.1
    
    have h2 : a.2 = b.2 := congrArg Prod.fst hab
    have hd : a.1 \ a.2 = b.1 \ b.2 := congrArg Prod.snd hab
    have ha1 : a.1 = a.2 ∪ (a.1 \ a.2) := (Finset.union_sdiff_of_subset haS).symm
    have hb1 : b.1 = b.2 ∪ (b.1 \ b.2) := (Finset.union_sdiff_of_subset hbS).symm
    apply Sigma.ext
    · rw [ha1, hb1, hd, h2]
    · rw [h2]
  · 
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    obtain ⟨hdisj, hn1src, hP⟩ := hp
    
    have hMmem : (p.1 ∪ p.2) ∈ s := (hs _).mpr ⟨Finset.subset_univ _, hP⟩
    have hSeven : p.1 ∈ gc45_evenSub ends (p.1 ∪ p.2) := by
      rw [gc45_evenSub, Finset.mem_filter, Finset.mem_powerset]
      exact ⟨Finset.subset_union_left, hn1src⟩
    refine ⟨⟨p.1 ∪ p.2, p.1⟩, ?_, ?_⟩
    · rw [Finset.mem_sigma]; exact ⟨hMmem, hSeven⟩
    · 
      have hdisj' : Disjoint p.1 p.2 := by
        rw [Finset.disjoint_left]; intro i hi1 hi2
        have := hdisj hi2; rw [Finset.mem_sdiff] at this; exact this.2 hi1
      have : (p.1 ∪ p.2) \ p.1 = p.2 := by
        rw [Finset.union_sdiff_left, Finset.sdiff_eq_self_of_disjoint hdisj'.symm]
      simp only [this]






theorem gc48_union_sources_eq_snd (ends : ι → Sym2 W) {p : Finset ι × Finset ι}
    (hdisj : p.2 ⊆ univ \ p.1) (hn1 : sources ends p.1 = (∅ : Finset W)) :
    sources ends (p.1 ∪ p.2) = sources ends p.2 := by
  have hd : Disjoint p.1 p.2 := by
    rw [Finset.disjoint_left]; intro i hi1 hi2
    have := hdisj hi2; rw [Finset.mem_sdiff] at this; exact this.2 hi1
  have hun : p.1 ∪ p.2 = p.1 ∆ p.2 := by rw [Disjoint.symmDiff_eq_sup hd]; rfl
  rw [hun, sources_symmDiff, hn1]
  rw [show (∅ : Finset W) = (⊥ : Finset W) from rfl, bot_symmDiff]





theorem gc48_LHSpairs_card_eq_doubled (ends : ι → Sym2 W) (o x y g : W) :
    #(gc47_LHSpairs ends o x y g) = #(gc48_LHSdoubled ends o x y g) := by
  rw [gc47_LHSpairs]
  rw [gc48_sigma_card_eq_doubled ends (gc43_Lset ends o x y g)
    (P := fun M => sources ends M = ({o, x} : Finset W) ∧ connK ends M x g)
    (fun M => by rw [gc43_Lset, Finset.mem_filter, Finset.mem_powerset])]
  rw [gc48_LHSdoubled]
  apply congrArg
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨hdisj, hn1, hsrc, hgate⟩
    rw [gc48_union_sources_eq_snd ends hdisj hn1] at hsrc
    exact ⟨hdisj, hn1, hsrc, hgate⟩
  · rintro ⟨hdisj, hn1, hsrc, hgate⟩
    rw [gc48_union_sources_eq_snd ends hdisj hn1]
    exact ⟨hdisj, hn1, hsrc, hgate⟩




theorem gc48_RHSpairs_card_eq_doubled (ends : ι → Sym2 W) (o x y g : W) :
    #(gc47_RHSpairs ends o x y g) = #(gc48_RHSdoubled ends o x y g) := by
  rw [gc47_RHSpairs]
  rw [gc48_sigma_card_eq_doubled ends (gc43_Rset ends o x y g)
    (P := fun M => sources ends M = ({o, x, y, g} : Finset W)
      ∧ connK ends M o x ∧ connK ends M o y ∧ connK ends M o g)
    (fun M => by rw [gc43_Rset, Finset.mem_filter, Finset.mem_powerset])]
  rw [gc48_RHSdoubled]
  apply congrArg
  apply Finset.filter_congr
  intro p _
  constructor
  · rintro ⟨hdisj, hn1, hsrc, hcx, hcy, hcg⟩
    rw [gc48_union_sources_eq_snd ends hdisj hn1] at hsrc
    exact ⟨hdisj, hn1, hsrc, hcx, hcy, hcg⟩
  · rintro ⟨hdisj, hn1, hsrc, hcx, hcy, hcg⟩
    rw [gc48_union_sources_eq_snd ends hdisj hn1]
    exact ⟨hdisj, hn1, hsrc, hcx, hcy, hcg⟩





theorem gc48_EMassResidue_iff_doubled_le (ends : ι → Sym2 W) (o x y g : W) :
    gc42_EMassResidue ends o x y g
      ↔ #(gc48_LHSdoubled ends o x y g) ≤ #(gc48_RHSdoubled ends o x y g) := by
  rw [gc47_EMassResidue_iff_pairCount_le, gc48_LHSpairs_card_eq_doubled,
    gc48_RHSpairs_card_eq_doubled]








theorem gc48_countIneq_of_pairCount_le (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hcard : #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g)) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc47_countIneq_of_pairInjection ends hnd hox hoy hog hxy hxg hyg huniv
    (gc48_pairInjection_of_pairCount_le ends o x y g hcard)

end Abstract















theorem gc48_defect_pairCount_le :
    #(gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3)
      ≤ #(gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) := by
  rw [gc47_defect_LHSpairs_card, gc47_defect_RHSpairs_card]





theorem gc48_defect_pairInjection_via_count :
    gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3 :=
  gc48_pairInjection_of_pairCount_le gc46_defectEnds (0 : Fin 4) 1 2 3 gc48_defect_pairCount_le



theorem gc48_defect_LHSdoubled_card :
    #(gc48_LHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
  rw [← gc48_LHSpairs_card_eq_doubled, gc47_defect_LHSpairs_card]



theorem gc48_defect_RHSdoubled_card :
    #(gc48_RHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
  rw [← gc48_RHSpairs_card_eq_doubled, gc47_defect_RHSpairs_card]



theorem gc48_defect_doubled_le :
    #(gc48_LHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3)
      ≤ #(gc48_RHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) := by
  rw [gc48_defect_LHSdoubled_card, gc48_defect_RHSdoubled_card]





theorem gc48_defect_summary :
    gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3
      ∧ #(gc48_LHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3)
          ≤ #(gc48_RHSdoubled gc46_defectEnds (0 : Fin 4) 1 2 3) :=
  ⟨gc48_defect_pairInjection_via_count, gc48_defect_doubled_le⟩

end StatMech.Walls
