/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































import Mathlib
import Code.Walls.gc66construct

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
set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]








theorem gc67b_degK_symmDiff_notMem (ends : ι → Sym2 W) (Q : Finset ι) {i : ι} {g : W}
    (hi : g ∉ ends i) :
    degK ends (Q ∆ ({i} : Finset ι)) g = degK ends Q g := by
  unfold degK
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_symmDiff, Finset.mem_singleton]
  constructor
  · rintro ⟨hj, hgj⟩
    rcases hj with ⟨hjQ, _⟩ | ⟨rfl, _⟩
    · exact ⟨hjQ, hgj⟩
    · exact absurd hgj hi
  · rintro ⟨hjQ, hgj⟩
    refine ⟨?_, hgj⟩
    by_cases hji : j = i
    · subst hji; exact absurd hgj hi
    · exact Or.inl ⟨hjQ, hji⟩












theorem gc67b_gdeg1_connector_of_conn (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {D : Finset ι} {y g : W} (hyg : y ≠ g) (hconn : connK ends D y g) :
    ∃ P, P ⊆ D ∧ sources ends P = ({y, g} : Finset W) ∧ degK ends P g = 1 := by
  
  suffices H : ∀ a : W, connK ends D a g → a ≠ g →
      ∃ P, P ⊆ D ∧ sources ends P = ({a, g} : Finset W) ∧ degK ends P g = 1 from
    H y hconn hyg
  intro a hwalk
  induction hwalk using Relation.ReflTransGen.head_induction_on with
  | refl =>
    
    intro hne; exact absurd rfl hne
  | @head a c hstep hrest ih =>
    intro hane
    obtain ⟨i, hiD, hai, hci, hac⟩ := hstep
    
    by_cases hcg : c = g
    · 
      have hgi : g ∈ ends i := hcg ▸ hci
      refine ⟨({i} : Finset ι), Finset.singleton_subset_iff.2 hiD, ?_, ?_⟩
      · 
        ext z
        simp only [mem_sources, degK, Finset.filter_singleton, Finset.mem_insert,
          Finset.mem_singleton]
        by_cases hz : z ∈ ends i
        · rw [if_pos hz, Finset.card_singleton]
          
          have hzag : z = a ∨ z = g := by
            obtain ⟨⟨p, q⟩, hpq⟩ := (ends i).exists_rep
            rw [← hpq] at hz hai hgi
            rw [Sym2.mem_iff] at hz hai hgi
            
            rcases hz with rfl | rfl <;> rcases hai with rfl | rfl <;> rcases hgi with rfl | rfl <;>
              tauto
          simp only [show Odd 1 from ⟨0, rfl⟩, true_iff]; exact hzag
        · rw [if_neg hz, Finset.card_empty]
          have : ¬ (z = a ∨ z = g) := by
            rintro (rfl | rfl)
            · exact hz hai
            · exact hz hgi
          simp only [show ¬ Odd 0 from by decide, false_iff]; exact this
      · rw [degK, Finset.filter_singleton, if_pos hgi, Finset.card_singleton]
    · 
      obtain ⟨Q, hQD, hQsrc, hQ1⟩ := ih hcg
      
      have hmem_ac : ∀ z, z ∈ ends i → z = a ∨ z = c := by
        intro z hz
        obtain ⟨⟨p, q⟩, hpq⟩ := (ends i).exists_rep
        rw [← hpq] at hz hai hci
        rw [Sym2.mem_iff] at hz hai hci
        rcases hz with rfl | rfl <;> rcases hai with rfl | rfl <;> rcases hci with rfl | rfl <;>
          tauto
      have hgi : g ∉ ends i := by
        intro hg
        rcases hmem_ac g hg with h | h
        · exact hane h.symm
        · exact hcg h.symm
      refine ⟨Q ∆ ({i} : Finset ι), ?_, ?_, ?_⟩
      · 
        intro j hj
        rw [Finset.mem_symmDiff] at hj
        rcases hj with ⟨hjQ, _⟩ | ⟨hji, _⟩
        · exact hQD hjQ
        · rw [Finset.mem_singleton] at hji; subst hji; exact hiD
      · 
        rw [sources_symmDiff, hQsrc]
        
        have hsi : sources ends ({i} : Finset ι) = ({a, c} : Finset W) := by
          ext z
          simp only [mem_sources, degK, Finset.filter_singleton, Finset.mem_insert,
            Finset.mem_singleton]
          by_cases hz : z ∈ ends i
          · rw [if_pos hz, Finset.card_singleton]
            have hzac : z = a ∨ z = c := by
              obtain ⟨⟨p, q⟩, hpq⟩ := (ends i).exists_rep
              rw [← hpq] at hz hai hci
              rw [Sym2.mem_iff] at hz hai hci
              rcases hz with rfl | rfl <;> rcases hai with rfl | rfl <;> rcases hci with rfl | rfl <;>
                tauto
            simp only [show Odd 1 from ⟨0, rfl⟩, true_iff]; exact hzac
          · rw [if_neg hz, Finset.card_empty]
            have : ¬ (z = a ∨ z = c) := by
              rintro (rfl | rfl)
              · exact hz hai
              · exact hz hci
            simp only [show ¬ Odd 0 from by decide, false_iff]; exact this
        rw [hsi]
        
        ext z
        simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (⟨hz, hz2⟩ | ⟨hz, hz2⟩)
          · 
            rcases hz with rfl | rfl
            · exact absurd (Or.inr rfl) hz2   
            · exact Or.inr rfl                
          · 
            rcases hz with rfl | rfl
            · exact Or.inl rfl                
            · exact absurd (Or.inl rfl) hz2   
        · rintro (rfl | rfl)
          · 
            right
            refine ⟨Or.inl rfl, ?_⟩
            rintro (h | h)
            · exact hac h                     
            · exact hane h                    
          · 
            left
            refine ⟨Or.inr rfl, ?_⟩
            rintro (h | h)
            · exact hane h.symm               
            · exact hcg h.symm                
      · 
        rw [gc67b_degK_symmDiff_notMem ends Q hgi]; exact hQ1















theorem gc67b_removableGEdge (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {y g : W} (hyg : y ≠ g) :
    gc66_RemovableGEdge ends K y g := by
  intro D hDV hDsrc hdeg2
  
  have hconn : connK ends D y g := gc66_ygConnector_connK ends hnd hyg hDsrc
  
  obtain ⟨P, hPD, hPsrc, hP1⟩ := gc67b_gdeg1_connector_of_conn ends hnd hyg hconn
  
  
  set gD : Finset ι := D.filter (fun i => g ∈ ends i) with hgD
  set gP : Finset ι := P.filter (fun i => g ∈ ends i) with hgP
  have hgPsub : gP ⊆ gD := by
    intro i hi
    rw [hgP, Finset.mem_filter] at hi
    rw [hgD, Finset.mem_filter]
    exact ⟨hPD hi.1, hi.2⟩
  have hcardgD : #gD = degK ends D g := rfl
  have hcardgP : #gP = degK ends P g := rfl
  
  have hlt : #gP < #gD := by rw [hcardgP, hcardgD, hP1]; omega
  have hne : (gD \ gP).Nonempty := by
    rw [← Finset.card_pos, Finset.card_sdiff_of_subset hgPsub]; omega
  obtain ⟨e, he⟩ := hne
  rw [Finset.mem_sdiff] at he
  obtain ⟨heD, hePc⟩ := he
  rw [hgD, Finset.mem_filter] at heD
  obtain ⟨heDmem, hegg⟩ := heD
  
  have hePnot : e ∉ P := by
    intro heP; exact hePc (by rw [hgP, Finset.mem_filter]; exact ⟨heP, hegg⟩)
  refine ⟨e, heDmem, hegg, ?_⟩
  
  have hPsub : P ⊆ D \ {e} := by
    intro i hi
    rw [Finset.mem_sdiff, Finset.mem_singleton]
    exact ⟨hPD hi, fun h => hePnot (h ▸ hi)⟩
  have hPconn : connK ends P y g := gc66_ygConnector_connK ends hnd hyg hPsrc
  exact mng_connK_mono ends hPsub hPconn






theorem gc67b_choose_D (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι)
    {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1 :=
  gc66_choose_D ends hnd K hoy hog hxy hxg hyg huniv hKsrc
    (gc67b_removableGEdge ends hnd K hyg)

end Abstract

open Classical










theorem gc67b_witness_removableGEdge :
    gc66_RemovableGEdge gc59_witnessEnds ({0} : Finset (Fin 5)) 2 3 :=
  gc67b_removableGEdge gc59_witnessEnds gc59_witnessEnds_loopless ({0} : Finset (Fin 5)) (by decide)






theorem gc67b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (y g : W),
        y ≠ g → gc66_RemovableGEdge ends K y g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        sources ends K = ({o, x} : Finset W) →
        ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1)
    ∧ 
    gc66_RemovableGEdge gc59_witnessEnds ({0} : Finset (Fin 5)) 2 3 :=
  ⟨fun ends hnd K y g hyg => gc67b_removableGEdge ends hnd K hyg,
    fun ends hnd K o x y g hoy hog hxy hxg hyg huniv hKsrc =>
      gc67b_choose_D ends hnd K hoy hog hxy hxg hyg huniv hKsrc,
    gc67b_witness_removableGEdge⟩

end StatMech.Walls
