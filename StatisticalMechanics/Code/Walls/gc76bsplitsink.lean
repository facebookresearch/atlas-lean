/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/













































































































import Mathlib
import Code.Walls.gc75bcyclespace

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
set_option maxHeartbeats 8000000
set_option maxRecDepth 20000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]














def gc76b_IsSplitCut (ends : ι → Sym2 W) (K L : Finset ι) (o y g : W) (C : Finset ι) : Prop :=
    C ⊆ K ∪ L ∧ ¬ connK ends ((K ∪ L) \ C) o g ∧ ¬ connK ends ((K ∪ L) \ C) y g







theorem gc76b_disjointConnectors_of_splitFlow (ends : ι → Sym2 W)
    {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPsrc : sources ends P = ({o, g} : Finset W))
    (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    ∃ P', P' ⊆ K ∪ L ∧ sources ends P' = ({o, g} : Finset W) ∧ Disjoint P' D ∧ connK ends P' o g :=
  ⟨P, hPG, hPsrc, hPD, hPconn⟩





theorem gc76b_survives_of_splitFlow (ends : ι → Sym2 W)
    {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn







theorem gc76b_splitCut_card_ge2_of_flow (ends : ι → Sym2 W)
    {K L : Finset ι} {o y g : W} {P₁ P₂ : Finset ι}
    (hP₁G : P₁ ⊆ K ∪ L) (hP₁conn : connK ends P₁ o g)
    (hP₂G : P₂ ⊆ K ∪ L) (hP₂conn : connK ends P₂ y g)
    (hdisj : Disjoint P₁ P₂)
    {C : Finset ι} (hC : gc76b_IsSplitCut ends K L o y g C) :
    2 ≤ #C := by
  obtain ⟨hCG, hCo, hCy⟩ := hC
  
  have hmeet₁ : (P₁ ∩ C).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hempty
    exact hCo (mng_connK_of_disjoint ends hP₁G hempty hP₁conn)
  have hmeet₂ : (P₂ ∩ C).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty, ← Finset.disjoint_iff_inter_eq_empty] at hempty
    exact hCy (mng_connK_of_disjoint ends hP₂G hempty hP₂conn)
  obtain ⟨a, ha⟩ := hmeet₁
  obtain ⟨b, hb⟩ := hmeet₂
  rw [Finset.mem_inter] at ha hb
  have hab : a ≠ b := by
    intro h; subst h
    exact (Finset.disjoint_left.1 hdisj) ha.1 hb.1
  have hsub : ({a, b} : Finset ι) ⊆ C := by
    intro z hz
    rw [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact ha.2
    · exact hb.2
  calc (2 : ℕ) = #({a, b} : Finset ι) := by rw [Finset.card_pair hab]
    _ ≤ #C := Finset.card_le_card hsub



end Abstract

open Classical




























noncomputable def gc76b_ssEnds : Fin 5 → Sym2 (Fin 4) :=
  ![s(0, 1), s(1, 2), s(1, 3), s(1, 3), s(1, 3)]

theorem gc76b_ssEnds_loopless : ∀ i : Fin 5, ¬ (gc76b_ssEnds i).IsDiag := by decide


theorem gc76b_ssEnds_univ_sources :
    sources gc76b_ssEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc76b_ssEnds_K_sources :
    sources gc76b_ssEnds ({0} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc76b_ssEnds_g_deg3 : degK gc76b_ssEnds (univ : Finset (Fin 5)) 3 = 3 := by decide




theorem gc76b_ssEnds_L23_sources :
    sources gc76b_ssEnds ({2, 3} : Finset (Fin 5)) = (∅ : Finset (Fin 4)) := by decide


theorem gc76b_ssEnds_gate_23 :
    connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) 1 3 :=
  Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc76b_ssEnds_gate_24 :
    connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) 1 3 :=
  Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩


theorem gc76b_ssEnds_gate_34 :
    connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 1 3 :=
  Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc76b_ssEnds_gate_fail_empty :
    ¬ connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ (∅ : Finset (Fin 5))) 1 3 := by
  rw [Finset.union_empty]
  intro h
  have inv : ∀ w : Fin 4, connK gc76b_ssEnds ({0} : Finset (Fin 5)) 1 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)





theorem gc76b_ssEnds_sourceEmpty :
    ({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
        (fun L => sources gc76b_ssEnds L = (∅ : Finset (Fin 4)))
      = ({∅, {2, 3}, {2, 4}, {3, 4}} : Finset (Finset (Fin 5))) := by decide



theorem gc76b_ssEnds_LblockSet :
    gc51_LblockSet gc76b_ssEnds ({0} : Finset (Fin 5)) 0 1 3
      = ({({2, 3} : Finset (Fin 5)), ({2, 4} : Finset (Fin 5)),
          ({3, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) := by
  rw [gc51_LblockSet]
  rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
  rw [show ({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
        (fun L => sources gc76b_ssEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ L) 1 3)
      = (({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
          (fun L => sources gc76b_ssEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [gc76b_ssEnds_sourceEmpty]
  ext L
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hLmem, hconn⟩
    rcases hLmem with rfl | rfl | rfl | rfl
    · exact absurd hconn gc76b_ssEnds_gate_fail_empty
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨by simp, gc76b_ssEnds_gate_23⟩
    · exact ⟨by simp, gc76b_ssEnds_gate_24⟩
    · exact ⟨by simp, gc76b_ssEnds_gate_34⟩




theorem gc76b_ssEnds_og_23 :
    connK gc76b_ssEnds (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) 0 3 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩



theorem gc76b_ssEnds_split_og_23 :
    ¬ connK gc76b_ssEnds
      ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))
        = ({2, 3} : Finset (Fin 5)) from by decide]
  intro h
  have inv : ∀ w : Fin 4, connK gc76b_ssEnds ({2, 3} : Finset (Fin 5)) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      subst ih
      fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide
  exact absurd (inv 3 h) (by decide)



theorem gc76b_ssEnds_split_yg_23 :
    ¬ connK gc76b_ssEnds
      ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 2 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))
        = ({2, 3} : Finset (Fin 5)) from by decide]
  intro h
  have inv : ∀ w : Fin 4, connK gc76b_ssEnds ({2, 3} : Finset (Fin 5)) 2 w → w = 2 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      subst ih
      fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide
  exact absurd (inv 3 h) (by decide)





theorem gc76b_ss_splitCut1_23 :
    gc76b_IsSplitCut gc76b_ssEnds ({0} : Finset (Fin 5)) ({2, 3} : Finset (Fin 5)) 0 2 3
      ({0} : Finset (Fin 5)) :=
  ⟨by decide, gc76b_ssEnds_split_og_23, gc76b_ssEnds_split_yg_23⟩





theorem gc76b_ssEnds_D_data :
    ({1, 2} : Finset (Fin 5)) ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5))
      ∧ sources gc76b_ssEnds ({1, 2} : Finset (Fin 5)) = ({2, 3} : Finset (Fin 4))
      ∧ degK gc76b_ssEnds ({1, 2} : Finset (Fin 5)) 3 = 1 := by
  refine ⟨?_, by decide, by decide⟩
  rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
  decide




theorem gc76b_ss_residue_23 :
    connK gc76b_ssEnds
      ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 3} : Finset (Fin 5)) from by decide]
  exact (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩



theorem gc76b_ss_residue_24 :
    connK gc76b_ssEnds
      ((({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 4} : Finset (Fin 5)) from by decide]
  exact (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨4, by decide, by decide, by decide, by decide⟩



theorem gc76b_ss_residue_34 :
    connK gc76b_ssEnds
      ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 3, 4} : Finset (Fin 5)) from by decide]
  exact (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩





theorem gc76b_ss_splitSink_refuted :
    gc76b_IsSplitCut gc76b_ssEnds ({0} : Finset (Fin 5)) ({2, 3} : Finset (Fin 5)) 0 2 3
        ({0} : Finset (Fin 5))
      ∧ #({0} : Finset (Fin 5)) = 1
      ∧ connK gc76b_ssEnds
          ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 :=
  ⟨gc76b_ss_splitCut1_23, by decide, gc76b_ss_residue_23⟩









theorem gc76b_ss_cutEdge_in_K :
    (0 : Fin 5) ∈ ({0} : Finset (Fin 5))
      ∧ (0 : Fin 5) ∉ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5))
      ∧ ({1, 2} : Finset (Fin 5)) ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) := by
  refine ⟨by decide, by decide, ?_⟩
  rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
  decide
















theorem gc76b_IrreducibleTwoCommodity {ι W : Type*} [DecidableEq ι] [Fintype ι]
    [DecidableEq W] [Fintype W] (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hog : o ≠ g) {D : Finset ι} :
    (∀ L ∈ gc51_LblockSet ends K o x g,
        ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g)
      ↔ (∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) :=
  gc75b_bridgeConnectors_iff_notCut (y := y) ends hnd K hog








theorem gc76b_ss_twoCommodityLeaf :
    gc71_TwoCommodityLeaf gc76b_ssEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine gc73b_twoCommodityLeaf_of_notCut gc76b_ssEnds gc76b_ssEnds_loopless
    ({0} : Finset (Fin 5)) (by decide) gc76b_ssEnds_D_data.1 gc76b_ssEnds_D_data.2.1
    gc76b_ssEnds_D_data.2.2 ?_
  intro L hL
  rw [gc76b_ssEnds_LblockSet] at hL
  simp only [Finset.mem_insert, Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl
  · exact gc76b_ss_residue_23
  · exact gc76b_ss_residue_24
  · exact gc76b_ss_residue_34











theorem gc76b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K L D P : Finset ι) (o g : W),
        P ⊆ K ∪ L → sources ends P = ({o, g} : Finset W) → Disjoint P D → connK ends P o g →
        ∃ P', P' ⊆ K ∪ L ∧ sources ends P' = ({o, g} : Finset W)
          ∧ Disjoint P' D ∧ connK ends P' o g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K L : Finset ι) (o y g : W) (P₁ P₂ : Finset ι),
        P₁ ⊆ K ∪ L → connK ends P₁ o g → P₂ ⊆ K ∪ L → connK ends P₂ y g → Disjoint P₁ P₂ →
        ∀ C : Finset ι, gc76b_IsSplitCut ends K L o y g C → 2 ≤ #C)
    ∧ 
    (gc76b_IsSplitCut gc76b_ssEnds ({0} : Finset (Fin 5)) ({2, 3} : Finset (Fin 5)) 0 2 3
        ({0} : Finset (Fin 5))
      ∧ #({0} : Finset (Fin 5)) = 1
      ∧ connK gc76b_ssEnds
          ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3)
    ∧ 
    gc71_TwoCommodityLeaf gc76b_ssEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends K L D P o g hPG hPsrc hPD hPconn =>
      gc76b_disjointConnectors_of_splitFlow ends hPG hPsrc hPD hPconn,
    fun ends K L o y g P₁ P₂ hP₁G hP₁conn hP₂G hP₂conn hdisj C hC =>
      gc76b_splitCut_card_ge2_of_flow ends hP₁G hP₁conn hP₂G hP₂conn hdisj hC,
    gc76b_ss_splitSink_refuted,
    gc76b_ss_twoCommodityLeaf⟩

end StatMech.Walls
