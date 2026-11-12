/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
















































































import Mathlib
import Code.Walls.gc53count

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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]






theorem gc54_gate_monotone (ends : ι → Sym2 W) (K : Finset ι) {m₁ m₂ : Finset ι} (h : m₁ ⊆ m₂)
    {x g : W} (hgate : connK ends (K ∪ m₁) x g) : connK ends (K ∪ m₂) x g :=
  gc51_connK_mono ends (Finset.union_subset_union_right h) hgate







theorem gc54_gate_disjoint_eq (ends : ι → Sym2 W) (K : Finset ι) {L P₀ : Finset ι}
    (hdisj : Disjoint L P₀) {x g : W} (hgate : connK ends (K ∪ L) x g) :
    connK ends (K ∪ (L ∆ P₀)) x g := by
  have hun : L ∆ P₀ = L ∪ P₀ := Disjoint.symmDiff_eq_sup hdisj
  rw [hun]
  exact gc54_gate_monotone ends K Finset.subset_union_left hgate





theorem gc54_LblockSet_eq (ends : ι → Sym2 W) (K : Finset ι) (o x g : W) :
    gc51_LblockSet ends K o x g
      = (univ \ K).powerset.filter
          (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ L) x g) := rfl



theorem gc54_cosetGateBlock_eq (ends : ι → Sym2 W) (K P₀ : Finset ι) (o x g : W) :
    gc53_cosetGateBlock ends K P₀ o x g
      = (univ \ K).powerset.filter
          (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ (L ∆ P₀)) x g) := rfl





















def gc54_GateShiftInjection (ends : ι → Sym2 W) (K P₀ : Finset ι) (o x g : W) : Prop :=
    ∃ C, C ⊆ univ \ K ∧ sources ends C = (∅ : Finset W)
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g, connK ends (K ∪ ((L ∆ C) ∆ P₀)) x g






theorem gc54_shift_mem_A (ends : ι → Sym2 W) {K C L : Finset ι}
    (hCV : C ⊆ univ \ K) (hCsrc : sources ends C = (∅ : Finset W)) {o x g : W}
    (hL : L ∈ gc51_LblockSet ends K o x g) :
    (L ∆ C) ⊆ univ \ K ∧ sources ends (L ∆ C) = (∅ : Finset W) := by
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨hLV, hLsrc, _⟩ := hL
  refine ⟨?_, ?_⟩
  · intro i hi
    rw [Finset.mem_symmDiff] at hi
    rcases hi with ⟨h, _⟩ | ⟨h, _⟩
    · exact hLV h
    · exact hCV h
  · rw [sources_symmDiff, hLsrc, hCsrc, symmDiff_self]; rfl


theorem gc54_shift_injOn (C : Finset ι) (s : Finset (Finset ι)) :
    Set.InjOn (fun L => L ∆ C) (s : Set (Finset ι)) := by
  intro a _ b _ hab
  simp only at hab
  have : (a ∆ C) ∆ C = (b ∆ C) ∆ C := by rw [hab]
  rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at this










theorem gc54_lblock_le_cosetGate_of_gateShiftInjection (ends : ι → Sym2 W)
    (K P₀ : Finset ι) {o x g : W}
    (h : gc54_GateShiftInjection ends K P₀ o x g) :
    #(gc51_LblockSet ends K o x g) ≤ #(gc53_cosetGateBlock ends K P₀ o x g) := by
  obtain ⟨C, hCV, hCsrc, hgate⟩ := h
  apply Finset.card_le_card_of_injOn (fun L => L ∆ C)
  · 
    intro L hL
    rw [Finset.mem_coe] at hL
    simp only [Finset.mem_coe, gc53_cosetGateBlock, Finset.mem_filter, Finset.mem_powerset]
    obtain ⟨hsub, hsrc⟩ := gc54_shift_mem_A ends hCV hCsrc hL
    exact ⟨hsub, hsrc, hgate L hL⟩
  · exact gc54_shift_injOn C _









theorem gc54_gateShiftInjection_of_identity (ends : ι → Sym2 W) (K P₀ : Finset ι) {o x g : W}
    (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L P₀) :
    gc54_GateShiftInjection ends K P₀ o x g := by
  have hsrc0 : sources ends (∅ : Finset ι) = (∅ : Finset W) := by
    ext v; simp [StatMech.Sharpness.RandomCurrent.sources, StatMech.Sharpness.RandomCurrent.degK]
  refine ⟨∅, Finset.empty_subset _, hsrc0, ?_⟩
  · intro L hL
    have hLmem := hL
    rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
    obtain ⟨_, _, hgate⟩ := hL
    rw [show (L ∆ (∅ : Finset ι)) = L from symmDiff_eq_left.mpr rfl]
    exact gc54_gate_disjoint_eq ends K (hdisj L hLmem) hgate






theorem gc54_cosetGateDom_of_gateShiftInjection (ends : ι → Sym2 W) {o x y g : W}
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        ∀ P₀ ⊆ univ \ K, sources ends P₀ = ({y, g} : Finset W) →
          gc54_GateShiftInjection ends K P₀ o x g) :
    gc53_CosetGateDom ends o x y g := by
  intro K hK P₀ hP₀sub hP₀src
  exact gc54_lblock_le_cosetGate_of_gateShiftInjection ends K P₀ (h K hK P₀ hP₀sub hP₀src)




theorem gc54_countIneq_of_gateShiftInjection (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        ∀ P₀ ⊆ univ \ K, sources ends P₀ = ({y, g} : Finset W) →
          gc54_GateShiftInjection ends K P₀ o x g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc53_countIneq_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv
    (gc54_cosetGateDom_of_gateShiftInjection ends h)

end Abstract

open Classical













theorem gc54_witness_gateShiftInjection_K13 (P₀ : Finset (Fin 4)) :
    gc54_GateShiftInjection gc49_witnessEnds ({1, 3} : Finset (Fin 4)) P₀ 0 1 3 := by
  apply gc54_gateShiftInjection_of_identity
  intro L hL
  rw [gc51_witness_LblockSet_K13, Finset.mem_singleton] at hL
  subst hL
  exact Finset.disjoint_empty_left P₀


theorem gc54_witness_gateShiftInjection_K23 (P₀ : Finset (Fin 4)) :
    gc54_GateShiftInjection gc49_witnessEnds ({2, 3} : Finset (Fin 4)) P₀ 0 1 3 := by
  apply gc54_gateShiftInjection_of_identity
  intro L hL
  rw [gc51_witness_LblockSet_K23, Finset.mem_singleton] at hL
  subst hL
  exact Finset.disjoint_empty_left P₀





theorem gc54_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc54_cosetGateDom_of_gateShiftInjection
  intro K hK P₀ hP₀sub hP₀src
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc54_witness_gateShiftInjection_K13 P₀
  · exact gc54_witness_gateShiftInjection_K23 P₀




theorem gc54_witness_perKCount : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc53_perKCount_of_cosetGateDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc49_witnessEnds_univ_sources gc54_witness_cosetGateDom

end StatMech.Walls
