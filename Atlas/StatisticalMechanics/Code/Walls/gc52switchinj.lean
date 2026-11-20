/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































import Mathlib
import Code.Walls.gc51minpath

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

open StatMech.Sharpness.RandomCurrent (sources connK sources_symmDiff)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]











theorem gc52_selector_complete (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {L Q : Finset ι} (hL : L ∈ gc51_LblockSet ends K o x g)
    (hQ : Q ∈ gc51_RblockSet ends K o x y g) :
    (L ∆ Q) ⊆ univ \ K ∧ sources ends (L ∆ Q) = ({y, g} : Finset W)
      ∧ (L ∆ (L ∆ Q)) ∈ gc51_RblockSet ends K o x y g := by
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨hLV, hLsrc, _⟩ := hL
  have hQV : Q ⊆ univ \ K := by
    rw [gc51_RblockSet, Finset.mem_filter, Finset.mem_powerset] at hQ
    exact hQ.1
  have hQsrc : sources ends Q = ({y, g} : Finset W) := by
    rw [gc51_RblockSet, Finset.mem_filter, Finset.mem_powerset] at hQ
    exact hQ.2.1
  refine ⟨?_, ?_, ?_⟩
  · 
    intro i hi
    rw [Finset.mem_symmDiff] at hi
    rcases hi with ⟨h, _⟩ | ⟨h, _⟩
    · exact hLV h
    · exact hQV h
  · 
    rw [sources_symmDiff, hLsrc, hQsrc]
    simp
  · 
    rw [symmDiff_symmDiff_cancel_left]
    exact hQ


















theorem gc52_switchInjective_of_card_le (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (hcard : #(gc51_LblockSet ends K o x g) ≤ #(gc51_RblockSet ends K o x y g)) :
    gc51_SwitchInjective ends K o x y g := by
  
  have hcard' : Fintype.card {L // L ∈ gc51_LblockSet ends K o x g}
      ≤ Fintype.card {Q // Q ∈ gc51_RblockSet ends K o x y g} := by
    simpa [Fintype.card_coe] using hcard
  obtain ⟨e⟩ := Function.Embedding.nonempty_iff_card_le.2 hcard'
  
  classical
  let F : Finset ι → Finset ι := fun L =>
    if h : L ∈ gc51_LblockSet ends K o x g then (e ⟨L, h⟩ : {Q // Q ∈ _}).1 else ∅
  have hFmem : ∀ L (h : L ∈ gc51_LblockSet ends K o x g),
      F L ∈ gc51_RblockSet ends K o x y g := by
    intro L h
    simp only [F, dif_pos h]
    exact (e ⟨L, h⟩).2
  have hFinj : ∀ L₁ (h₁ : L₁ ∈ gc51_LblockSet ends K o x g)
      L₂ (h₂ : L₂ ∈ gc51_LblockSet ends K o x g), F L₁ = F L₂ → L₁ = L₂ := by
    intro L₁ h₁ L₂ h₂ hEq
    simp only [F, dif_pos h₁, dif_pos h₂] at hEq
    have : e ⟨L₁, h₁⟩ = e ⟨L₂, h₂⟩ := Subtype.ext hEq
    have := e.injective this
    exact congrArg Subtype.val this
  
  refine ⟨fun L => L ∆ F L, ?_, ?_⟩
  · 
    intro L hL
    obtain ⟨hsub, hsrc, hmaps⟩ := gc52_selector_complete ends K hL (hFmem L hL)
    refine ⟨hsub, hsrc, ?_⟩
    
    rw [symmDiff_symmDiff_cancel_left] at hmaps ⊢
    exact hmaps
  · 
    intro L₁ hL₁ L₂ hL₂ hEq
    rw [Finset.mem_coe] at hL₁ hL₂
    simp only [symmDiff_symmDiff_cancel_left] at hEq
    exact hFinj L₁ hL₁ L₂ hL₂ hEq






theorem gc52_card_le_of_switchInjective (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc51_SwitchInjective ends K o x y g) :
    #(gc51_LblockSet ends K o x g) ≤ #(gc51_RblockSet ends K o x y g) := by
  have := gc51_perK_dom_of_switchInjective ends K h
  rwa [← gc51_LblockSet_card, ← gc51_RblockSet_card] at this





theorem gc52_switchInjective_iff_card_le (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W} :
    gc51_SwitchInjective ends K o x y g
      ↔ #(gc51_LblockSet ends K o x g) ≤ #(gc51_RblockSet ends K o x y g) :=
  ⟨gc52_card_le_of_switchInjective ends K, gc52_switchInjective_of_card_le ends K⟩


theorem gc52_switchInjective_iff_gc50_count (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W} :
    gc51_SwitchInjective ends K o x y g
      ↔ gc50_Lblock ends K o x g ≤ gc50_Rblock ends K o x y g := by
  rw [gc52_switchInjective_iff_card_le, gc51_LblockSet_card, gc51_RblockSet_card]







def gc52_PerKCount (ends : ι → Sym2 W) (o x y g : W) : Prop :=
    ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      gc50_Lblock ends K o x g ≤ gc50_Rblock ends K o x y g


theorem gc52_perKCount_iff_perKDom (ends : ι → Sym2 W) {o x y g : W} :
    gc52_PerKCount ends o x y g ↔ gc50_PerKDom ends o x y g := Iff.rfl


theorem gc52_switchInjective_of_perKCount (ends : ι → Sym2 W) {o x y g : W}
    (h : gc52_PerKCount ends o x y g) :
    ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      gc51_SwitchInjective ends K o x y g := by
  intro K hK
  exact (gc52_switchInjective_iff_gc50_count ends K).2 (h K hK)





theorem gc52_countIneq_of_perKCount (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : gc52_PerKCount ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc51_countIneq_of_switchInjective ends hnd hox hoy hog hxy hxg hyg huniv
    (gc52_switchInjective_of_perKCount ends h)

end Abstract

open Classical










theorem gc52_witness_count_K13 :
    #(gc51_LblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 3)
      ≤ #(gc51_RblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3) := by
  rw [gc51_witness_LblockSet_K13, gc51_witness_RblockSet_K13, Finset.card_singleton,
    Finset.card_singleton]


theorem gc52_witness_count_K23 :
    #(gc51_LblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 3)
      ≤ #(gc51_RblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3) := by
  rw [gc51_witness_LblockSet_K23, gc51_witness_RblockSet_K23, Finset.card_singleton,
    Finset.card_singleton]




theorem gc52_witness_switchInjective_K13_via_count :
    gc51_SwitchInjective gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 :=
  gc52_switchInjective_of_card_le gc49_witnessEnds _ gc52_witness_count_K13


theorem gc52_witness_switchInjective_K23_via_count :
    gc51_SwitchInjective gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 :=
  gc52_switchInjective_of_card_le gc49_witnessEnds _ gc52_witness_count_K23






theorem gc52_witness_perKDom : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rw [← gc51_LblockSet_card, ← gc51_RblockSet_card]
  rcases hK with rfl | rfl
  · exact gc52_witness_count_K13
  · exact gc52_witness_count_K23

end StatMech.Walls
