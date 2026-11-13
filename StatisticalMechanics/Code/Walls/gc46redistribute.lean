/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































import Mathlib
import Code.Walls.gc45cycle

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false
set_option linter.style.multiGoal false
set_option maxHeartbeats 1600000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
















theorem gc46_card_symmDiff_closed_eq_two_pow (F : Finset (Finset ι))
    (h0 : (∅ : Finset ι) ∈ F) (hclosed : ∀ a ∈ F, ∀ b ∈ F, a ∆ b ∈ F) :
    ∃ n : ℕ, #F = 2 ^ n := by
  induction F using Finset.strongInduction with
  | _ F ih =>
    by_cases hsing : ∀ x ∈ F, x = (∅ : Finset ι)
    · 
      refine ⟨0, ?_⟩
      have hFeq : F = {(∅ : Finset ι)} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr ⟨h0, hsing⟩
      rw [hFeq, Finset.card_singleton, pow_zero]
    · 
      push Not at hsing
      obtain ⟨a, haF, hane⟩ := hsing
      obtain ⟨i, hia⟩ := hane
      
      set H := F.filter (fun x => i ∉ x) with hH
      
      have h0H : (∅ : Finset ι) ∈ H := by
        rw [hH, Finset.mem_filter]; exact ⟨h0, Finset.notMem_empty i⟩
      
      have hclosedH : ∀ x ∈ H, ∀ y ∈ H, x ∆ y ∈ H := by
        intro x hx y hy
        rw [hH, Finset.mem_filter] at hx hy ⊢
        refine ⟨hclosed x hx.1 y hy.1, ?_⟩
        intro hcontra
        rw [Finset.mem_symmDiff] at hcontra
        rcases hcontra with ⟨h, _⟩ | ⟨h, _⟩
        · exact hx.2 h
        · exact hy.2 h
      
      have hHsubF : H ⊆ F := Finset.filter_subset _ _
      have haH : a ∉ H := by rw [hH, Finset.mem_filter]; push Not; intro _; exact hia
      have hHssF : H ⊂ F := Finset.ssubset_iff_of_subset hHsubF |>.mpr ⟨a, haF, haH⟩
      obtain ⟨k, hk⟩ := ih H hHssF h0H hclosedH
      
      have hsplit : #(F.filter (fun x => i ∉ x)) + #(F.filter (fun x => i ∈ x)) = #F := by
        have := Finset.card_filter_add_card_filter_not (s := F) (p := fun x => i ∈ x)
        rw [add_comm] at this
        simpa using this
      
      have hbij : #(F.filter (fun x => i ∉ x)) = #(F.filter (fun x => i ∈ x)) := by
        apply Finset.card_nbij' (fun x => x ∆ a) (fun x => x ∆ a)
        · 
          intro x hx
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
          refine ⟨hclosed x hx.1 a haF, ?_⟩
          rw [Finset.mem_symmDiff]
          exact Or.inr ⟨hia, hx.2⟩
        · 
          intro x hx
          simp only [Finset.coe_filter, Set.mem_setOf_eq] at hx ⊢
          refine ⟨hclosed x hx.1 a haF, ?_⟩
          rw [Finset.mem_symmDiff]; push Not
          exact ⟨fun _ => hia, fun _ => hx.2⟩
        · 
          intro x hx
          simp only [symmDiff_symmDiff_cancel_right]
        · 
          intro x hx
          simp only [symmDiff_symmDiff_cancel_right]
      
      refine ⟨k + 1, ?_⟩
      rw [← hsplit, ← hbij, ← hH, hk]
      ring













theorem gc46_E_eq_two_pow_nullity (ends : ι → Sym2 W) (M : Finset ι) :
    ∃ n : ℕ, gc40_E ends M = 2 ^ n := by
  rw [gc45_E_eq_card_evenSub]
  exact gc46_card_symmDiff_closed_eq_two_pow (gc45_evenSub ends M)
    (gc45_empty_mem_evenSub ends M)
    (fun a ha b hb => gc45_evenSub_symmDiff_mem ends M ha hb)



theorem gc46_E_pos (ends : ι → Sym2 W) (M : Finset ι) : 1 ≤ gc40_E ends M := by
  obtain ⟨n, hn⟩ := gc46_E_eq_two_pow_nullity ends M
  rw [hn]
  exact Nat.one_le_two_pow




theorem gc46_E_eq_two_pow_log (ends : ι → Sym2 W) (M : Finset ι) :
    gc40_E ends M = 2 ^ (Nat.log 2 (gc40_E ends M)) := by
  obtain ⟨n, hn⟩ := gc46_E_eq_two_pow_nullity ends M
  rw [hn, Nat.log_pow (by norm_num)]
















theorem gc46_sameBoundary_subfamily_card_le_E (ends : ι → Sym2 W) (M' : Finset ι) (b : Finset W)
    (𝓕 : Finset (Finset ι))
    (hsub : ∀ M ∈ 𝓕, M ⊆ M')
    (hbd : ∀ M ∈ 𝓕, sources ends M = b) :
    #𝓕 ≤ gc40_E ends M' := by
  rw [gc45_E_eq_card_evenSub]
  rcases Finset.eq_empty_or_nonempty 𝓕 with hempty | ⟨M₀, hM₀⟩
  · simp [hempty]
  · 
    apply Finset.card_le_card_of_injOn (fun M => M ∆ M₀)
    · 
      intro M hM
      simp only [Finset.mem_coe] at hM
      simp only [Finset.mem_coe, gc45_evenSub, Finset.mem_filter, Finset.mem_powerset]
      refine ⟨?_, ?_⟩
      · 
        intro i hi
        rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨hiM, _⟩ | ⟨hiM₀, _⟩
        · exact hsub M hM hiM
        · exact hsub M₀ hM₀ hiM₀
      · 
        rw [sources_symmDiff, hbd M hM, hbd M₀ hM₀, symmDiff_self]; rfl
    · 
      intro a _ c _ hac
      exact symmDiff_left_injective M₀ hac







theorem gc46_fibre_card_le_E (ends : ι → Sym2 W) (o x y g : W)
    (φ : Finset ι → Finset ι)
    (hsub : ∀ M ∈ gc43_Lset ends o x y g, M ⊆ φ M)
    {M' : Finset ι} (hM' : M' ∈ gc43_Rset ends o x y g) :
    #((gc43_Lset ends o x y g).filter (fun M => φ M = M')) ≤ gc40_E ends M' := by
  apply gc46_sameBoundary_subfamily_card_le_E ends M' ({o, x} : Finset W)
  · 
    intro M hM
    rw [Finset.mem_filter] at hM
    obtain ⟨hML, hφM⟩ := hM
    have := hsub M hML
    rw [hφM] at this
    exact this
  · 
    intro M hM
    rw [Finset.mem_filter, gc43_Lset, Finset.mem_filter, Finset.mem_powerset] at hM
    exact hM.1.2.1







theorem gc46_fibreDomReloc_of_treeLHS_subset (ends : ι → Sym2 W) (o x y g : W)
    (htree : gc45_TreeLHS ends o x y g)
    (φ : Finset ι → Finset ι)
    (hmaps : ∀ M ∈ gc43_Lset ends o x y g, φ M ∈ gc43_Rset ends o x y g)
    (hsub : ∀ M ∈ gc43_Lset ends o x y g, M ⊆ φ M) :
    gc43_FibreDomReloc ends o x y g := by
  apply gc45_fibreDomReloc_of_count_le ends o x y g htree φ hmaps
  intro M' hM'
  exact gc46_fibre_card_le_E ends o x y g φ hsub hM'

end Abstract







































noncomputable def gc46_defectEnds : Fin 5 → Sym2 (Fin 4) := ![s(2, 3), s(2, 3), s(2, 3), s(0, 3), s(1, 3)]


theorem gc46_defectEnds_loopless : ∀ i : Fin 5, ¬ (gc46_defectEnds i).IsDiag := by decide


theorem gc46_defectEnds_univ_sources :
    sources gc46_defectEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide




theorem gc46_defect_Lset :
    gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3
      = {({3, 4} : Finset (Fin 5)), {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}} := by
  rw [gc43_Lset, ← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 5)).powerset.filter
        (fun M => sources gc46_defectEnds M = ({0, 1} : Finset (Fin 4))))
      = {({3, 4} : Finset (Fin 5)), {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}} from by decide]
  
  have g1 : connK gc46_defectEnds ({3, 4} : Finset (Fin 5)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
  have g2 : connK gc46_defectEnds ({0, 1, 3, 4} : Finset (Fin 5)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
  have g3 : connK gc46_defectEnds ({0, 2, 3, 4} : Finset (Fin 5)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
  have g4 : connK gc46_defectEnds ({1, 2, 3, 4} : Finset (Fin 5)) (1 : Fin 4) (3 : Fin 4) :=
    Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
    if_pos g1, if_pos g2, if_pos g3, if_pos g4]





theorem gc46_defect_Rset :
    gc43_Rset gc46_defectEnds (0 : Fin 4) 1 2 3
      = {({0, 3, 4} : Finset (Fin 5)), {1, 3, 4}, {2, 3, 4}, univ} := by
  rw [gc43_Rset, ← Finset.filter_filter]
  rw [show ((univ : Finset (Fin 5)).powerset.filter
        (fun M => sources gc46_defectEnds M = ({0, 1, 2, 3} : Finset (Fin 4))))
      = {({0, 3, 4} : Finset (Fin 5)), {1, 3, 4}, {2, 3, 4}, univ} from by decide]
  
  
  have gate034 : connK gc46_defectEnds ({0, 3, 4} : Finset (Fin 5)) 0 1
      ∧ connK gc46_defectEnds ({0, 3, 4} : Finset (Fin 5)) 0 2
      ∧ connK gc46_defectEnds ({0, 3, 4} : Finset (Fin 5)) 0 3 := by
    refine ⟨?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  have gate134 : connK gc46_defectEnds ({1, 3, 4} : Finset (Fin 5)) 0 1
      ∧ connK gc46_defectEnds ({1, 3, 4} : Finset (Fin 5)) 0 2
      ∧ connK gc46_defectEnds ({1, 3, 4} : Finset (Fin 5)) 0 3 := by
    refine ⟨?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  have gate234 : connK gc46_defectEnds ({2, 3, 4} : Finset (Fin 5)) 0 1
      ∧ connK gc46_defectEnds ({2, 3, 4} : Finset (Fin 5)) 0 2
      ∧ connK gc46_defectEnds ({2, 3, 4} : Finset (Fin 5)) 0 3 := by
    refine ⟨?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  have gateU : connK gc46_defectEnds (univ : Finset (Fin 5)) 0 1
      ∧ connK gc46_defectEnds (univ : Finset (Fin 5)) 0 2
      ∧ connK gc46_defectEnds (univ : Finset (Fin 5)) 0 3 := by
    refine ⟨?_, ?_, ?_⟩
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.head (b := (3 : Fin 4))
        ⟨3, by decide, by decide, by decide, by decide⟩
        (Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩)
    · exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_insert, Finset.filter_insert, Finset.filter_insert, Finset.filter_singleton,
    if_pos gate034, if_pos gate134, if_pos gate234, if_pos gateU]





theorem gc46_defect_EMassResidue : gc42_EMassResidue gc46_defectEnds (0 : Fin 4) 1 2 3 := by
  unfold gc42_EMassResidue
  rw [gc43_LHS_eq_gatedSum, gc43_RHS_eq_gatedSum, gc46_defect_Lset, gc46_defect_Rset]
  
  have hL : (∑ M ∈ ({({3, 4} : Finset (Fin 5)), {0, 1, 3, 4}, {0, 2, 3, 4}, {1, 2, 3, 4}} :
      Finset (Finset (Fin 5))), gc40_E gc46_defectEnds M) = 7 := by decide
  have hR : (∑ M ∈ ({({0, 3, 4} : Finset (Fin 5)), {1, 3, 4}, {2, 3, 4}, univ} :
      Finset (Finset (Fin 5))), gc40_E gc46_defectEnds M) = 7 := by decide
  rw [hL, hR]











theorem gc46_defect_not_FibreDomReloc :
    ¬ gc43_FibreDomReloc gc46_defectEnds (0 : Fin 4) 1 2 3 := by
  rintro ⟨φ, hmaps, hfib⟩
  
  have hmem : ∀ M ∈ ({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} :
      Finset (Finset (Fin 5))), M ∈ gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3 := by
    intro M hM; rw [gc46_defect_Lset]
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hM
    rcases hM with h | h | h <;> subst h <;> decide
  
  have hE2 : ∀ M ∈ ({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} :
      Finset (Finset (Fin 5))), φ M = univ := by
    intro M hM
    have hφmem := hmaps M (hmem M hM)
    rw [gc46_defect_Rset, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hφmem
    
    
    have hEM : gc40_E gc46_defectEnds M = 2 := by
      rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at hM
      rcases hM with h | h | h <;> subst h <;> decide
    rcases hφmem with h | h | h | h
    · exfalso
      have := hfib ({0, 3, 4} : Finset (Fin 5)) (by rw [gc46_defect_Rset]; decide)
      have hle : gc40_E gc46_defectEnds M ≤ 1 := by
        rw [show gc40_E gc46_defectEnds ({0, 3, 4} : Finset (Fin 5)) = 1 from by decide] at this
        calc gc40_E gc46_defectEnds M
            ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
                (fun N => φ N = ({0, 3, 4} : Finset (Fin 5))), gc40_E gc46_defectEnds N :=
              Finset.single_le_sum (f := fun N => gc40_E gc46_defectEnds N)
                (fun _ _ => Nat.zero_le _)
                (by rw [Finset.mem_filter]; exact ⟨hmem M hM, h⟩)
          _ ≤ 1 := this
      omega
    · exfalso
      have := hfib ({1, 3, 4} : Finset (Fin 5)) (by rw [gc46_defect_Rset]; decide)
      have hle : gc40_E gc46_defectEnds M ≤ 1 := by
        rw [show gc40_E gc46_defectEnds ({1, 3, 4} : Finset (Fin 5)) = 1 from by decide] at this
        calc gc40_E gc46_defectEnds M
            ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
                (fun N => φ N = ({1, 3, 4} : Finset (Fin 5))), gc40_E gc46_defectEnds N :=
              Finset.single_le_sum (f := fun N => gc40_E gc46_defectEnds N)
                (fun _ _ => Nat.zero_le _)
                (by rw [Finset.mem_filter]; exact ⟨hmem M hM, h⟩)
          _ ≤ 1 := this
      omega
    · exfalso
      have := hfib ({2, 3, 4} : Finset (Fin 5)) (by rw [gc46_defect_Rset]; decide)
      have hle : gc40_E gc46_defectEnds M ≤ 1 := by
        rw [show gc40_E gc46_defectEnds ({2, 3, 4} : Finset (Fin 5)) = 1 from by decide] at this
        calc gc40_E gc46_defectEnds M
            ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
                (fun N => φ N = ({2, 3, 4} : Finset (Fin 5))), gc40_E gc46_defectEnds N :=
              Finset.single_le_sum (f := fun N => gc40_E gc46_defectEnds N)
                (fun _ _ => Nat.zero_le _)
                (by rw [Finset.mem_filter]; exact ⟨hmem M hM, h⟩)
          _ ≤ 1 := this
      omega
    · exact h
  
  have hunivbound := hfib (univ : Finset (Fin 5)) (by rw [gc46_defect_Rset]; decide)
  rw [show gc40_E gc46_defectEnds (univ : Finset (Fin 5)) = 4 from by decide] at hunivbound
  
  have hsub3 : ({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} :
      Finset (Finset (Fin 5)))
      ⊆ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter (fun N => φ N = univ) := by
    intro M hM
    rw [Finset.mem_filter]
    exact ⟨hmem M hM, hE2 M hM⟩
  have hmass : (6 : ℕ) ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
      (fun N => φ N = univ), gc40_E gc46_defectEnds N := by
    calc (6 : ℕ)
        = ∑ N ∈ ({({0, 1, 3, 4} : Finset (Fin 5)), {0, 2, 3, 4}, {1, 2, 3, 4}} :
            Finset (Finset (Fin 5))), gc40_E gc46_defectEnds N := by decide
      _ ≤ ∑ N ∈ (gc43_Lset gc46_defectEnds (0 : Fin 4) 1 2 3).filter
            (fun N => φ N = univ), gc40_E gc46_defectEnds N :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub3 (fun _ _ _ => Nat.zero_le _)
  omega





theorem gc46_fibreDomReloc_strictly_stronger :
    gc42_EMassResidue gc46_defectEnds (0 : Fin 4) 1 2 3
      ∧ ¬ gc43_FibreDomReloc gc46_defectEnds (0 : Fin 4) 1 2 3 :=
  ⟨gc46_defect_EMassResidue, gc46_defect_not_FibreDomReloc⟩

end StatMech.Walls
