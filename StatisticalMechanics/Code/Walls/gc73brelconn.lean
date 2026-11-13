/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































































import Mathlib
import Code.Walls.gc72twogedge

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











theorem gc73b_perLClause_of_notCut (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o g : W} (hog : o ≠ g)
    (hsurv : connK ends ((K ∪ L) \ D) o g) :
    ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g :=
  gc72_trim_to_ogBoundary ends hnd hog hsurv




theorem gc73b_notCut_of_perLClause (ends : ι → Sym2 W)
    {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn




theorem gc73b_twoCommodityLeaf_of_notCut (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hog : o ≠ g)
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hnotcut : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  refine ⟨D, hDV, hDsrc, hD1, ?_⟩
  intro L hL
  exact gc73b_perLClause_of_notCut ends hnd hog (hnotcut L hL)















theorem gc73b_notCut_of_relConn (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L : Finset ι} {o g : W} (hog : o ≠ g)
    (hconn : connK ends (K ∪ L) o g)
    (hrel : ∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) →
        connK ends ((K ∪ L) \ P₁) o g)
    {D : Finset ι}
    (hDsub : ∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁) :
    connK ends ((K ∪ L) \ D) o g := by
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ :=
    gc72_ogSurvives_of_relConn ends hnd hog hconn hrel hDsub
  exact mng_connK_of_disjoint ends hPG hPD hPconn







theorem gc73b_twoCommodityLeaf_of_relConn_perL (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hrel : ∀ L ∈ gc51_LblockSet ends K o x g,
        (∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) →
            connK ends ((K ∪ L) \ P₁) o g)
          ∧ (∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁)) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  refine gc73b_twoCommodityLeaf_of_notCut ends hnd K hog hDV hDsrc hD1 ?_
  intro L hL
  obtain ⟨hrelL, hDsubL⟩ := hrel L hL
  have hconn : connK ends (K ∪ L) o g := gc72_og_in_KL ends hnd K hox hKsrc hL
  exact gc73b_notCut_of_relConn ends hnd hog hconn hrelL hDsubL















theorem gc73b_gcopyRemoval_of_fullRemoval (ends : ι → Sym2 W) {K L D : Finset ι} {eD : ι} {o g : W}
    (heD : eD ∈ D) (hsurv : connK ends ((K ∪ L) \ D) o g) :
    connK ends ((K ∪ L) \ ({eD} : Finset ι)) o g := by
  apply mng_connK_mono ends _ hsurv
  intro i hi
  rw [Finset.mem_sdiff] at hi ⊢
  refine ⟨hi.1, ?_⟩
  simp only [Finset.mem_singleton]
  intro h; subst h; exact hi.2 heD

end Abstract

open Classical















noncomputable def gc73b_brEnds : Fin 5 → Sym2 (Fin 4) :=
  ![s(0, 1), s(0, 2), s(0, 3), s(1, 3), s(1, 3)]

theorem gc73b_brEnds_loopless : ∀ i : Fin 5, ¬ (gc73b_brEnds i).IsDiag := by decide


theorem gc73b_brEnds_univ_sources :
    sources gc73b_brEnds (univ : Finset (Fin 5)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc73b_brEnds_K_sources :
    sources gc73b_brEnds ({0} : Finset (Fin 5)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc73b_brEnds_L_sources :
    sources gc73b_brEnds ({3, 4} : Finset (Fin 5)) = (∅ : Finset (Fin 4)) := by decide



theorem gc73b_brEnds_gate :
    connK gc73b_brEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 1 3 :=
  Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc73b_brEnds_og_conn :
    connK gc73b_brEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 0 3 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩




theorem gc73b_brEnds_bridge_cut :
    ¬ connK gc73b_brEnds
      ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))
        = ({3, 4} : Finset (Fin 5)) from by decide]
  intro h
  
  have inv : ∀ w : Fin 4, connK gc73b_brEnds ({3, 4} : Finset (Fin 5)) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail c d _ hstep ih =>
      obtain ⟨i, hi, hci, hdi, hcd⟩ := hstep
      subst ih
      fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide
  exact absurd (inv 3 h) (by decide)













theorem gc73b_bridge_edge_not_gEdge :
    connK gc73b_brEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 0 3
    ∧ (¬ connK gc73b_brEnds
        ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3)
    ∧ (3 : Fin 4) ∉ gc73b_brEnds 0 :=
  ⟨gc73b_brEnds_og_conn, gc73b_brEnds_bridge_cut, by decide⟩










theorem gc73b_gc59_surv_23 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 3} : Finset (Fin 5)) from by decide]
  exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc73b_gc59_surv_24 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 4} : Finset (Fin 5)) from by decide]
  exact Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩


theorem gc73b_gc59_surv_34 :
    connK gc59_witnessEnds ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))) 0 3 := by
  rw [show (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({1, 2} : Finset (Fin 5))
        = ({0, 3, 4} : Finset (Fin 5)) from by decide]
  exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩




theorem gc73b_witness_twoCommodityLeaf :
    gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine gc73b_twoCommodityLeaf_of_notCut gc59_witnessEnds gc59_witnessEnds_loopless
    ({0} : Finset (Fin 5)) (by decide) ?_ gc59_witnessEnds_D_sources gc65_witness_D_gDeg1 ?_
  · rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
    decide
  · intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact gc73b_gc59_surv_23
    · exact gc73b_gc59_surv_24
    · exact gc73b_gc59_surv_34








theorem gc73b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W)
      (D : Finset ι),
        o ≠ g → D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 →
        (∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) →
        gc71_TwoCommodityLeaf ends K o x y g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L : Finset ι) (o g : W),
        o ≠ g → connK ends (K ∪ L) o g →
        (∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) →
            connK ends ((K ∪ L) \ P₁) o g) →
        ∀ {D : Finset ι},
          (∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁) →
          connK ends ((K ∪ L) \ D) o g)
    ∧ 
    (connK gc73b_brEnds (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) 0 3
      ∧ (¬ connK gc73b_brEnds
          ((({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) \ ({0} : Finset (Fin 5))) 0 3)
      ∧ (3 : Fin 4) ∉ gc73b_brEnds 0)
    ∧ 
    gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends hnd K o x y g D hog hDV hDsrc hD1 hnotcut =>
      gc73b_twoCommodityLeaf_of_notCut ends hnd K hog hDV hDsrc hD1 hnotcut,
    fun ends hnd K L o g hog hconn hrel D hDsub =>
      gc73b_notCut_of_relConn ends hnd hog hconn hrel hDsub,
    gc73b_bridge_edge_not_gEdge,
    gc73b_witness_twoCommodityLeaf⟩

end StatMech.Walls
