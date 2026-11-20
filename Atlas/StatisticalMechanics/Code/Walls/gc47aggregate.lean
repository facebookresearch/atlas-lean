/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































import Mathlib
import Code.Walls.gc46redistribute

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







noncomputable def gc47_LHSpairs (ends : ι → Sym2 W) (o x y g : W) :
    Finset (Σ _ : Finset ι, Finset ι) :=
  (gc43_Lset ends o x y g).sigma (fun M => gc45_evenSub ends M)



noncomputable def gc47_RHSpairs (ends : ι → Sym2 W) (o x y g : W) :
    Finset (Σ _ : Finset ι, Finset ι) :=
  (gc43_Rset ends o x y g).sigma (fun M => gc45_evenSub ends M)




theorem gc47_gatedSum_eq_sigma_card (ends : ι → Sym2 W) (s : Finset (Finset ι)) :
    (∑ M ∈ s, gc40_E ends M) = #(s.sigma (fun M => gc45_evenSub ends M)) := by
  rw [Finset.card_sigma]
  exact Finset.sum_congr rfl (fun M _ => gc45_E_eq_card_evenSub ends M)





theorem gc47_LHSpairs_card (ends : ι → Sym2 W) (o x y g : W) :
    (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x} : Finset W)),
        (if connK ends M x g then gc40_E ends M else 0))
      = #(gc47_LHSpairs ends o x y g) := by
  rw [gc43_LHS_eq_gatedSum, gc47_LHSpairs, gc47_gatedSum_eq_sigma_card]



theorem gc47_RHSpairs_card (ends : ι → Sym2 W) (o x y g : W) :
    (∑ M ∈ (univ : Finset ι).powerset.filter (fun S => sources ends S = ({o, x, y, g} : Finset W)),
        (if connK ends M o x ∧ connK ends M o y ∧ connK ends M o g then gc40_E ends M else 0))
      = #(gc47_RHSpairs ends o x y g) := by
  rw [gc43_RHS_eq_gatedSum, gc47_RHSpairs, gc47_gatedSum_eq_sigma_card]




theorem gc47_EMassResidue_iff_pairCount_le (ends : ι → Sym2 W) (o x y g : W) :
    gc42_EMassResidue ends o x y g
      ↔ #(gc47_LHSpairs ends o x y g) ≤ #(gc47_RHSpairs ends o x y g) := by
  unfold gc42_EMassResidue
  rw [gc47_LHSpairs_card, gc47_RHSpairs_card]





















def gc47_PairInjection (ends : ι → Sym2 W) (o x y g : W) : Prop :=
  ∃ Φ : (Σ _ : Finset ι, Finset ι) → (Σ _ : Finset ι, Finset ι),
    (∀ p ∈ gc47_LHSpairs ends o x y g, Φ p ∈ gc47_RHSpairs ends o x y g)
      ∧ Set.InjOn Φ (gc47_LHSpairs ends o x y g)




theorem gc47_EMassResidue_of_pairInjection (ends : ι → Sym2 W) (o x y g : W)
    (h : gc47_PairInjection ends o x y g) :
    gc42_EMassResidue ends o x y g := by
  obtain ⟨Φ, hmap, hinj⟩ := h
  rw [gc47_EMassResidue_iff_pairCount_le]
  exact Finset.card_le_card_of_injOn Φ hmap hinj




theorem gc47_countIneq_of_pairInjection (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : gc47_PairInjection ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc42_countIneq_of_EMass ends hnd hox hoy hog hxy hxg hyg huniv
    (gc47_EMassResidue_of_pairInjection ends o x y g h)

end Abstract














theorem gc47_defect_LHSpairs_card :
    #(gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
  rw [gc47_LHSpairs, gc46_defect_Lset]; decide



theorem gc47_defect_RHSpairs_card :
    #(gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) = 7 := by
  rw [gc47_RHSpairs, gc46_defect_Rset]; decide









def gc47_defectΦ : (Σ _ : Finset (Fin 5), Finset (Fin 5)) → (Σ _ : Finset (Fin 5), Finset (Fin 5)) :=
  fun p =>
    if p.1 = ({3, 4} : Finset (Fin 5)) ∧ p.2 = (∅ : Finset (Fin 5)) then ⟨univ, ∅⟩
    else if p.1 = ({0, 1, 3, 4} : Finset (Fin 5)) ∧ p.2 = (∅ : Finset (Fin 5)) then ⟨{0, 3, 4}, ∅⟩
    else if p.1 = ({0, 2, 3, 4} : Finset (Fin 5)) ∧ p.2 = (∅ : Finset (Fin 5)) then ⟨{1, 3, 4}, ∅⟩
    else if p.1 = ({1, 2, 3, 4} : Finset (Fin 5)) ∧ p.2 = (∅ : Finset (Fin 5)) then ⟨{2, 3, 4}, ∅⟩
    else if p.1 = ({0, 1, 3, 4} : Finset (Fin 5)) ∧ p.2 = ({0, 1} : Finset (Fin 5)) then ⟨univ, {0, 1}⟩
    else if p.1 = ({0, 2, 3, 4} : Finset (Fin 5)) ∧ p.2 = ({0, 2} : Finset (Fin 5)) then ⟨univ, {0, 2}⟩
    else ⟨univ, {1, 2}⟩



theorem gc47_defectΦ_mapsTo :
    ∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
      gc47_defectΦ p ∈ gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3 := by
  rw [gc47_LHSpairs, gc46_defect_Lset, gc47_RHSpairs, gc46_defect_Rset]; decide



theorem gc47_defectΦ_injOn :
    Set.InjOn gc47_defectΦ (gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3) := by
  intro a ha b hb hab
  have hdec : ∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
      ∀ q ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
        gc47_defectΦ p = gc47_defectΦ q → p = q := by
    rw [gc47_LHSpairs, gc46_defect_Lset]; decide
  exact hdec a ha b hb hab





theorem gc47_defect_pairInjection :
    gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3 :=
  ⟨gc47_defectΦ, gc47_defectΦ_mapsTo, gc47_defectΦ_injOn⟩




theorem gc47_defect_EMassResidue_via_pairs :
    gc42_EMassResidue gc46_defectEnds (0 : Fin 4) 1 2 3 :=
  gc47_EMassResidue_of_pairInjection gc46_defectEnds (0 : Fin 4) 1 2 3 gc47_defect_pairInjection





noncomputable def gc47_defectOverflow : Finset (Σ _ : Finset (Fin 5), Finset (Fin 5)) :=
  (({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} : Finset (Finset (Fin 5)))).sigma
    (fun M => gc45_evenSub gc46_defectEnds M)


theorem gc47_defectOverflow_card : #gc47_defectOverflow = 6 := by decide


theorem gc47_defectOverflow_subset :
    gc47_defectOverflow ⊆ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3 := by
  rw [gc47_LHSpairs, gc46_defect_Lset, gc47_defectOverflow]
  intro p hp; revert p; decide


theorem gc47_defect_univFibre_card :
    #(({(univ : Finset (Fin 5))} : Finset (Finset (Fin 5))).sigma
        (fun M => gc45_evenSub gc46_defectEnds M)) = 4 := by decide












theorem gc47_defect_no_subset_pairInjection :
    ¬ ∃ Φ : (Σ _ : Finset (Fin 5), Finset (Fin 5)) → (Σ _ : Finset (Fin 5), Finset (Fin 5)),
        (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
            Φ p ∈ gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3)
          ∧ Set.InjOn Φ (gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3)
          ∧ (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3, p.1 ⊆ (Φ p).1) := by
  rintro ⟨Φ, hmap, hinj, hsub⟩
  
  have hUniv : ∀ p ∈ gc47_defectOverflow,
      Φ p ∈ ({(univ : Finset (Fin 5))} : Finset (Finset (Fin 5))).sigma
        (fun M => gc45_evenSub gc46_defectEnds M) := by
    intro p hp
    have hpL := gc47_defectOverflow_subset hp
    have hΦR := hmap p hpL
    have hΦsub := hsub p hpL
    
    rw [gc47_RHSpairs, Finset.mem_sigma] at hΦR
    obtain ⟨hΦR1, hΦR2⟩ := hΦR
    
    have hp1 : p.1 = ({0, 1, 3, 4} : Finset (Fin 5)) ∨ p.1 = ({0, 2, 3, 4} : Finset (Fin 5))
        ∨ p.1 = ({1, 2, 3, 4} : Finset (Fin 5)) := by
      rw [gc47_defectOverflow, Finset.mem_sigma] at hp
      have := hp.1
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at this
      exact this
    have hΦ1univ : (Φ p).1 = (univ : Finset (Fin 5)) := by
      
      have hRexp : (Φ p).1 ∈ ({({0, 3, 4} : Finset (Fin 5)), {1, 3, 4}, {2, 3, 4}, univ} :
          Finset (Finset (Fin 5))) := by
        rw [← gc46_defect_Rset]; exact hΦR1
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hRexp
      
      rcases hp1 with h | h | h <;> rw [h] at hΦsub <;>
        rcases hRexp with hR | hR | hR | hR <;> rw [hR] at hΦsub ⊢ <;>
          first
            | rfl
            | (exfalso; revert hΦsub; decide)
    rw [Finset.mem_sigma, Finset.mem_singleton, hΦ1univ]
    exact ⟨rfl, by rw [hΦ1univ] at hΦR2; exact hΦR2⟩
  
  have hle := Finset.card_le_card_of_injOn Φ hUniv
    (Set.InjOn.mono (by exact_mod_cast gc47_defectOverflow_subset) hinj)
  rw [gc47_defectOverflow_card, gc47_defect_univFibre_card] at hle
  omega






theorem gc47_defect_pairLevel_splits :
    gc47_PairInjection gc46_defectEnds (0 : Fin 4) 1 2 3
      ∧ ¬ ∃ Φ : (Σ _ : Finset (Fin 5), Finset (Fin 5)) → (Σ _ : Finset (Fin 5), Finset (Fin 5)),
          (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3,
              Φ p ∈ gc47_RHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3)
            ∧ Set.InjOn Φ (gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3)
            ∧ (∀ p ∈ gc47_LHSpairs gc46_defectEnds (0 : Fin 4) 1 2 3, p.1 ⊆ (Φ p).1) :=
  ⟨gc47_defect_pairInjection, gc47_defect_no_subset_pairInjection⟩

end StatMech.Walls
