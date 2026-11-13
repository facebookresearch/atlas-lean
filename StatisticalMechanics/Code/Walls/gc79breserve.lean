/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




































































































import Mathlib
import Code.Walls.gc78bxside

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










def gc79b_gEdges (ends : ι → Sym2 W) (D : Finset ι) (g : W) : Finset ι :=
    D.filter (fun i => g ∈ ends i)



theorem gc79b_reservedGEdge_exists (ends : ι → Sym2 W) {D : Finset ι} {g : W}
    (hD1 : degK ends D g = 1) :
    ∃ eY, gc79b_gEdges ends D g = {eY} ∧ eY ∈ D ∧ g ∈ ends eY := by
  have hcard : #(gc79b_gEdges ends D g) = 1 := hD1
  rw [Finset.card_eq_one] at hcard
  obtain ⟨eY, heY⟩ := hcard
  have hmem : eY ∈ gc79b_gEdges ends D g := by rw [heY]; exact Finset.mem_singleton_self eY
  rw [gc79b_gEdges, Finset.mem_filter] at hmem
  exact ⟨eY, heY, hmem.1, hmem.2⟩






theorem gc79b_leaf_of_reservedSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hog : o ≠ g)
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) :
    gc71_TwoCommodityLeaf ends K o x y g :=
  gc73b_twoCommodityLeaf_of_notCut ends hnd K hog hDV hDsrc hD1 hsurv





theorem gc79b_leaf_of_reservedSurvival_xg (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  refine gc79b_leaf_of_reservedSurvival ends hnd K hog hDV hDsrc hD1 ?_
  intro L hL
  exact (gc78b_xgSurvives_iff_ogSurvives ends hnd hox hKsrc hDV).1 (hsurv L hL)

end Abstract

open Classical













noncomputable def gc79b_pathEnds : Fin 2 → Sym2 (Fin 3) := ![s(0, 2), s(1, 2)]

theorem gc79b_pathEnds_loopless : ∀ i : Fin 2, ¬ (gc79b_pathEnds i).IsDiag := by decide



theorem gc79b_pathEnds_boundary :
    sources gc79b_pathEnds (univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 3)) := by decide


theorem gc79b_pathEnds_og :
    connK gc79b_pathEnds (univ : Finset (Fin 2)) 0 2 :=
  Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩


theorem gc79b_pathEnds_xg :
    connK gc79b_pathEnds (univ : Finset (Fin 2)) 1 2 :=
  Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩





theorem gc79b_path_removeGEdge_cuts_o :
    ¬ connK gc79b_pathEnds ((univ : Finset (Fin 2)) \ ({0} : Finset (Fin 2))) 0 2 := by
  rw [show (univ : Finset (Fin 2)) \ ({0} : Finset (Fin 2)) = ({1} : Finset (Fin 2)) from by decide]
  intro h
  have inv : ∀ w : Fin 3, connK gc79b_pathEnds ({1} : Finset (Fin 2)) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      subst ih
      fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide
  exact absurd (inv 2 h) (by decide)




theorem gc79b_single_gEdge_survival_false :
    sources gc79b_pathEnds (univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 3))
    ∧ connK gc79b_pathEnds (univ : Finset (Fin 2)) 0 2
    ∧ connK gc79b_pathEnds (univ : Finset (Fin 2)) 1 2
    ∧ (¬ connK gc79b_pathEnds ((univ : Finset (Fin 2)) \ ({0} : Finset (Fin 2))) 0 2) :=
  ⟨gc79b_pathEnds_boundary, gc79b_pathEnds_og, gc79b_pathEnds_xg, gc79b_path_removeGEdge_cuts_o⟩
























theorem gc79b_xEnds_workingD_reserved :
    gc79b_gEdges gc78b_xEnds ({5, 6} : Finset (Fin 7)) 3 = ({6} : Finset (Fin 7))
      ∧ (6 : Fin 7) ∈ ({5, 6} : Finset (Fin 7))
      ∧ (3 : Fin 5) ∈ gc78b_xEnds 6 := by
  refine ⟨by decide, by decide, by decide⟩





theorem gc79b_xEnds_gate_34 :
    connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({3, 4} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({3, 4} : Finset (Fin 7))) = ({2, 3, 4} : Finset (Fin 7)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_gate_0134 :
    connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 1, 3, 4} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 1, 3, 4} : Finset (Fin 7))) = ({0, 1, 2, 3, 4} : Finset (Fin 7)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_gate_0356 :
    connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) = ({0, 2, 3, 5, 6} : Finset (Fin 7)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_gate_0456 :
    connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 4, 5, 6} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 4, 5, 6} : Finset (Fin 7))) = ({0, 2, 4, 5, 6} : Finset (Fin 7)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩).tail
    ⟨4, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_gate_1356 :
    connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({1, 3, 5, 6} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({1, 3, 5, 6} : Finset (Fin 7))) = ({1, 2, 3, 5, 6} : Finset (Fin 7)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_gate_1456 :
    connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) = ({1, 2, 4, 5, 6} : Finset (Fin 7)) from by decide]
  exact (Relation.ReflTransGen.single (b := (0 : Fin 5))
      ⟨2, by decide, by decide, by decide, by decide⟩).tail
    ⟨4, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_gate_fail_empty :
    ¬ connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ (∅ : Finset (Fin 7))) 1 3 := by
  rw [Finset.union_empty]
  intro h
  have inv : ∀ w : Fin 5, connK gc78b_xEnds ({2} : Finset (Fin 7)) 1 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)



theorem gc79b_xEnds_gate_fail_01 :
    ¬ connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ ({0, 1} : Finset (Fin 7))) 1 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 1} : Finset (Fin 7))) = ({0, 1, 2} : Finset (Fin 7)) from by decide]
  intro h
  have inv : ∀ w : Fin 5, connK gc78b_xEnds ({0, 1, 2} : Finset (Fin 7)) 1 w → (w = 0 ∨ w = 1 ∨ w = 2) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 | h3 <;> exact absurd h3 (by decide)





theorem gc79b_xEnds_sourceEmpty :
    ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)).powerset.filter
        (fun L => sources gc78b_xEnds L = (∅ : Finset (Fin 5)))
      = ({∅, {0, 1}, {3, 4}, {0, 1, 3, 4}, {0, 3, 5, 6}, {0, 4, 5, 6},
          {1, 3, 5, 6}, {1, 4, 5, 6}} : Finset (Finset (Fin 7))) := by decide




theorem gc79b_xEnds_LblockSet :
    gc51_LblockSet gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 3
      = ({({3, 4} : Finset (Fin 7)), ({0, 1, 3, 4} : Finset (Fin 7)),
          ({0, 3, 5, 6} : Finset (Fin 7)), ({0, 4, 5, 6} : Finset (Fin 7)),
          ({1, 3, 5, 6} : Finset (Fin 7)), ({1, 4, 5, 6} : Finset (Fin 7))}
            : Finset (Finset (Fin 7))) := by
  rw [gc51_LblockSet]
  rw [show (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7)) = ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)) from by decide]
  rw [show ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)).powerset.filter
        (fun L => sources gc78b_xEnds L = (∅ : Finset (Fin 5))
          ∧ connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ L) 1 3)
      = (({0, 1, 3, 4, 5, 6} : Finset (Fin 7)).powerset.filter
          (fun L => sources gc78b_xEnds L = (∅ : Finset (Fin 5)))).filter
            (fun L => connK gc78b_xEnds (({2} : Finset (Fin 7)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [gc79b_xEnds_sourceEmpty]
  ext L
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hLmem, hconn⟩
    rcases hLmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact absurd hconn gc79b_xEnds_gate_fail_empty
    · exact absurd hconn gc79b_xEnds_gate_fail_01
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact ⟨by decide, gc79b_xEnds_gate_34⟩
    · exact ⟨by decide, gc79b_xEnds_gate_0134⟩
    · exact ⟨by decide, gc79b_xEnds_gate_0356⟩
    · exact ⟨by decide, gc79b_xEnds_gate_0456⟩
    · exact ⟨by decide, gc79b_xEnds_gate_1356⟩
    · exact ⟨by decide, gc79b_xEnds_gate_1456⟩





theorem gc79b_xEnds_D_data :
    ({5, 6} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7))
      ∧ sources gc78b_xEnds ({5, 6} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
      ∧ degK gc78b_xEnds ({5, 6} : Finset (Fin 7)) 3 = 1 := by
  refine ⟨?_, by decide, by decide⟩
  rw [show (univ : Finset (Fin 7)) \ ({2} : Finset (Fin 7)) = ({0, 1, 3, 4, 5, 6} : Finset (Fin 7)) from by decide]
  decide


theorem gc79b_xEnds_surv_34 :
    connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({3, 4} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({3, 4} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
        = ({2, 3, 4} : Finset (Fin 7)) from by decide]
  exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_surv_0134 :
    connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 1, 3, 4} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 1, 3, 4} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
        = ({0, 1, 2, 3, 4} : Finset (Fin 7)) from by decide]
  exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩



theorem gc79b_xEnds_surv_0356 :
    connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
        = ({0, 2, 3} : Finset (Fin 7)) from by decide]
  exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_surv_0456 :
    connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 4, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 4, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
        = ({0, 2, 4} : Finset (Fin 7)) from by decide]
  exact Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_surv_1356 :
    connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({1, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({1, 3, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
        = ({1, 2, 3} : Finset (Fin 7)) from by decide]
  exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc79b_xEnds_surv_1456 :
    connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({5, 6} : Finset (Fin 7))
        = ({1, 2, 4} : Finset (Fin 7)) from by decide]
  exact Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩




theorem gc79b_xEnds_workingD_survives_all :
    ∀ L ∈ gc51_LblockSet gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 3,
      connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ L) \ ({5, 6} : Finset (Fin 7))) 0 3 := by
  intro L hL
  rw [gc79b_xEnds_LblockSet] at hL
  simp only [Finset.mem_insert, Finset.mem_singleton] at hL
  rcases hL with rfl | rfl | rfl | rfl | rfl | rfl
  · exact gc79b_xEnds_surv_34
  · exact gc79b_xEnds_surv_0134
  · exact gc79b_xEnds_surv_0356
  · exact gc79b_xEnds_surv_0456
  · exact gc79b_xEnds_surv_1356
  · exact gc79b_xEnds_surv_1456





theorem gc79b_xEnds_twoCommodityLeaf :
    gc71_TwoCommodityLeaf gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 2 3 :=
  gc79b_leaf_of_reservedSurvival gc78b_xEnds gc78b_xEnds_loopless ({2} : Finset (Fin 7))
    (by decide) gc79b_xEnds_D_data.1 gc79b_xEnds_D_data.2.1 gc79b_xEnds_D_data.2.2
    gc79b_xEnds_workingD_survives_all





theorem gc79b_xEnds_minCard_03_fails :
    ¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 0 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))
        = ({2, 5, 6} : Finset (Fin 7)) from by decide]
  intro h
  have inv : ∀ w : Fin 5, connK gc78b_xEnds ({2, 5, 6} : Finset (Fin 7)) 0 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)




theorem gc79b_xEnds_minCard_14_fails :
    ¬ connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({1, 4} : Finset (Fin 7))) 0 3 := by
  rw [show (({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({1, 4} : Finset (Fin 7))
        = ({2, 5, 6} : Finset (Fin 7)) from by decide]
  intro h
  have inv : ∀ w : Fin 5, connK gc78b_xEnds ({2, 5, 6} : Finset (Fin 7)) 0 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)









theorem gc79b_xEnds_Luniformity_verdict :
    
    (∀ L ∈ gc51_LblockSet gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 3,
        connK gc78b_xEnds ((({2} : Finset (Fin 7)) ∪ L) \ ({5, 6} : Finset (Fin 7))) 0 3)
      
      ∧ (¬ connK gc78b_xEnds
          ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 0 3)
      ∧ (¬ connK gc78b_xEnds
          ((({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({1, 4} : Finset (Fin 7))) 0 3) :=
  ⟨gc79b_xEnds_workingD_survives_all, gc79b_xEnds_minCard_03_fails, gc79b_xEnds_minCard_14_fails⟩











theorem gc79b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W)
      (D : Finset ι),
        o ≠ g → D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 →
        (∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) →
        gc71_TwoCommodityLeaf ends K o x y g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (D : Finset ι) (g : W),
        degK ends D g = 1 →
        ∃ eY, gc79b_gEdges ends D g = {eY} ∧ eY ∈ D ∧ g ∈ ends eY)
    ∧ 
    (sources gc79b_pathEnds (univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 3))
      ∧ connK gc79b_pathEnds (univ : Finset (Fin 2)) 0 2
      ∧ connK gc79b_pathEnds (univ : Finset (Fin 2)) 1 2
      ∧ (¬ connK gc79b_pathEnds ((univ : Finset (Fin 2)) \ ({0} : Finset (Fin 2))) 0 2))
    ∧ 
    gc71_TwoCommodityLeaf gc78b_xEnds ({2} : Finset (Fin 7)) 0 1 2 3
    ∧ 
    ((¬ connK gc78b_xEnds
        ((({2} : Finset (Fin 7)) ∪ ({0, 3, 5, 6} : Finset (Fin 7))) \ ({0, 3} : Finset (Fin 7))) 0 3)
      ∧ (¬ connK gc78b_xEnds
          ((({2} : Finset (Fin 7)) ∪ ({1, 4, 5, 6} : Finset (Fin 7))) \ ({1, 4} : Finset (Fin 7))) 0 3)) :=
  ⟨fun ends hnd K o x y g D hog hDV hDsrc hD1 hsurv =>
      gc79b_leaf_of_reservedSurvival ends hnd K hog hDV hDsrc hD1 hsurv,
    fun ends D g hD1 => gc79b_reservedGEdge_exists ends hD1,
    gc79b_single_gEdge_survival_false,
    gc79b_xEnds_twoCommodityLeaf,
    ⟨gc79b_xEnds_minCard_03_fails, gc79b_xEnds_minCard_14_fails⟩⟩

end StatMech.Walls
