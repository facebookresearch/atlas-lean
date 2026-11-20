/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































































import Mathlib
import Code.Walls.gc70sharedsink

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












theorem gc71_room_of_gDeg1 (ends : ι → Sym2 W) {D : Finset ι} {g : W}
    (hge3 : 3 ≤ degK ends (univ : Finset ι) g) (hD1 : degK ends D g = 1) :
    2 ≤ degK ends ((univ : Finset ι) \ D) g :=
  gc65_gDegGe3_room ends hge3 hD1





theorem gc71_minConnector_gDeg1 (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {y g : W} (hyg : y ≠ g) {D : Finset ι} (hDV : D ⊆ univ \ K)
    (hDsrc : sources ends D = ({y, g} : Finset W))
    (hDmin : ∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D') :
    degK ends D g = 1 :=
  gc69b_minConnector_gDeg1 ends hnd K hyg hDV hDsrc hDmin











theorem gc71_gc66_of_gDeg1Data (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hsurv : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g) :
    gc66_GDeg1RemovalSurvival ends K o x y g :=
  ⟨D, hDV, hDsrc, hD1, hsurv⟩




theorem gc71_countIneq_of_removalSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc66_GDeg1RemovalSurvival ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc66_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv h









def gc71_TwoCommodityLeaf (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g,
          ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W)
            ∧ Disjoint P D ∧ connK ends P o g




theorem gc71_gc66_of_twoCommodityLeaf (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc71_TwoCommodityLeaf ends K o x y g) :
    gc66_GDeg1RemovalSurvival ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hD1, hL⟩ := h
  refine ⟨D, hDV, hDsrc, hD1, ?_⟩
  intro L hLmem
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ := hL L hLmem
  have hog' : connK ends ((K ∪ L) \ D) o g := mng_connK_of_disjoint ends hPG hPD hPconn
  exact gc68_xg_survives_of_og ends hnd hox hKsrc hDV hog'



theorem gc71_countIneq_of_twoCommodityLeaf (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc71_TwoCommodityLeaf ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc71_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc71_gc66_of_twoCommodityLeaf ends hnd K hox hKsrc (h K hK)

end Abstract

open Classical















noncomputable def ceEnds : Fin 10 → Sym2 (Fin 6) :=
  ![s(0, 3), s(4, 5), s(2, 5), s(3, 4), s(0, 1), s(0, 5), s(2, 5), s(1, 3), s(0, 1), s(0, 2)]

theorem ceEnds_loopless : ∀ i : Fin 10, ¬ (ceEnds i).IsDiag := by decide


theorem ceEnds_univ_sources :
    sources ceEnds (univ : Finset (Fin 10)) = ({0, 1, 2, 3} : Finset (Fin 6)) := by decide


theorem ceEnds_K_sources :
    sources ceEnds ({4} : Finset (Fin 10)) = ({0, 1} : Finset (Fin 6)) := by decide


theorem ceEnds_V_eq :
    (univ : Finset (Fin 10)) \ ({4} : Finset (Fin 10))
      = ({0, 1, 2, 3, 5, 6, 7, 8, 9} : Finset (Fin 10)) := by decide



theorem ceEnds_no_lowCard :
    ((({0, 1, 2, 3, 5, 6, 7, 8, 9} : Finset (Fin 10)).powerset.filter (fun D => #D ≤ 1)).filter
      (fun D => sources ceEnds D = ({2, 3} : Finset (Fin 6)))) = (∅ : Finset (Finset (Fin 10))) := by
  decide




theorem ceEnds_card2_unique :
    ((({0, 1, 2, 3, 5, 6, 7, 8, 9} : Finset (Fin 10)).powerset.filter (fun D => #D ≤ 2)).filter
      (fun D => sources ceEnds D = ({2, 3} : Finset (Fin 6)))) = {({0, 9} : Finset (Fin 10))} := by
  decide



theorem ceEnds_minCard_unique {D' : Finset (Fin 10)}
    (hD'V : D' ⊆ ({0, 1, 2, 3, 5, 6, 7, 8, 9} : Finset (Fin 10)))
    (hD'src : sources ceEnds D' = ({2, 3} : Finset (Fin 6))) (hD'card : #D' ≤ 2) :
    D' = ({0, 9} : Finset (Fin 10)) := by
  have hmem : D' ∈ ({({0, 9} : Finset (Fin 10))} : Finset (Finset (Fin 10))) := by
    rw [← ceEnds_card2_unique, Finset.mem_filter, Finset.mem_filter, Finset.mem_powerset]
    exact ⟨⟨hD'V, hD'card⟩, hD'src⟩
  simpa using hmem


theorem ceEnds_D09_sources :
    sources ceEnds ({0, 9} : Finset (Fin 10)) = ({2, 3} : Finset (Fin 6)) := by decide


theorem ceEnds_D09_subset :
    ({0, 9} : Finset (Fin 10)) ⊆ (univ : Finset (Fin 10)) \ ({4} : Finset (Fin 10)) := by decide


theorem ceEnds_L_sources :
    sources ceEnds ({0, 1, 2, 3, 9} : Finset (Fin 10)) = (∅ : Finset (Fin 6)) := by decide


theorem ceEnds_L_subset :
    ({0, 1, 2, 3, 9} : Finset (Fin 10)) ⊆ (univ : Finset (Fin 10)) \ ({4} : Finset (Fin 10)) := by
  decide



theorem ceEnds_gate :
    connK ceEnds (({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 6))
      ⟨4, by decide, by decide, by decide, by decide⟩).tail
    ⟨0, by decide, by decide, by decide, by decide⟩



theorem ceEnds_not_conn_of_invariant (G : Finset (Fin 10)) {a b : Fin 6} (C : Fin 6 → Prop)
    [DecidablePred C] (hCa : C a) (hCb : ¬ C b)
    (hclosed : ∀ c d : Fin 6, C c →
      (∃ i ∈ G, c ∈ ceEnds i ∧ d ∈ ceEnds i ∧ c ≠ d) → C d) :
    ¬ connK ceEnds G a b := by
  intro h
  have inv : ∀ w : Fin 6, connK ceEnds G a w → C w := by
    intro w hw
    induction hw with
    | refl => exact hCa
    | @tail c d _ hstep ih => exact hclosed c d ih hstep
  exact hCb (inv b h)



theorem ceEnds_D09_fails :
    ¬ connK ceEnds
      ((({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))) \ ({0, 9} : Finset (Fin 10)))
      0 3 := by
  rw [show (({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))) \ ({0, 9} : Finset (Fin 10))
        = ({1, 2, 3, 4} : Finset (Fin 10)) from by decide]
  refine ceEnds_not_conn_of_invariant _ (fun w => w = 0 ∨ w = 1) (by decide) (by decide) ?_
  intro c d hc ⟨i, hi, hci, hdi, hcd⟩
  rcases hc with rfl | rfl <;> (fin_cases hi <;> revert hcd hci hdi <;> revert d <;> decide)


theorem ceEnds_L_mem :
    ({0, 1, 2, 3, 9} : Finset (Fin 10))
      ∈ gc51_LblockSet ceEnds ({4} : Finset (Fin 10)) 0 1 3 := by
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨by rw [ceEnds_V_eq]; decide, ceEnds_L_sources, ceEnds_gate⟩







theorem gc71_minCardResidue_false :
    ¬ gc70b_OGConnAvoidingD ceEnds ({4} : Finset (Fin 10)) 0 1 2 3 := by
  rintro ⟨D, hDV, hDsrc, hDmin, hL⟩
  
  have h09V : ({0, 9} : Finset (Fin 10)) ⊆ univ \ ({4} : Finset (Fin 10)) := ceEnds_D09_subset
  have hle : #D ≤ #({0, 9} : Finset (Fin 10)) := hDmin _ h09V ceEnds_D09_sources
  have hcard2 : #({0, 9} : Finset (Fin 10)) = 2 := by decide
  have hDle2 : #D ≤ 2 := by omega
  have hDV' : D ⊆ ({0, 1, 2, 3, 5, 6, 7, 8, 9} : Finset (Fin 10)) := by
    rw [← ceEnds_V_eq]; exact hDV
  have hDeq : D = ({0, 9} : Finset (Fin 10)) := ceEnds_minCard_unique hDV' hDsrc hDle2
  subst hDeq
  
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ := hL ({0, 1, 2, 3, 9} : Finset (Fin 10)) ceEnds_L_mem
  exact ceEnds_D09_fails (mng_connK_of_disjoint ceEnds hPG hPD hPconn)



theorem gc71_ogSurvival_false :
    ¬ gc69b_OGSurvival ceEnds ({4} : Finset (Fin 10)) 0 1 2 3 := by
  intro h
  exact gc71_minCardResidue_false
    ((gc70b_ogConnAvoidingD_iff_ogSurvival ceEnds ceEnds_loopless ({4} : Finset (Fin 10))
      (by decide) (by decide) ceEnds_K_sources).2 h)










theorem ceEnds_D123_sources :
    sources ceEnds ({1, 2, 3} : Finset (Fin 10)) = ({2, 3} : Finset (Fin 6)) := by decide


theorem ceEnds_D123_gDeg1 :
    degK ceEnds ({1, 2, 3} : Finset (Fin 10)) 3 = 1 := by decide


theorem ceEnds_D123_subset :
    ({1, 2, 3} : Finset (Fin 10)) ⊆ (univ : Finset (Fin 10)) \ ({4} : Finset (Fin 10)) := by decide


theorem ceEnds_D123_notMinCard :
    #({0, 9} : Finset (Fin 10)) < #({1, 2, 3} : Finset (Fin 10)) := by decide



theorem ceEnds_P0_sources :
    sources ceEnds ({0} : Finset (Fin 10)) = ({0, 3} : Finset (Fin 6)) := by decide


theorem ceEnds_P0_conn : connK ceEnds ({0} : Finset (Fin 10)) 0 3 :=
  Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩






theorem gc71_ce_gDeg1_witness :
    ∃ D', D' ⊆ univ \ ({4} : Finset (Fin 10)) ∧ sources ceEnds D' = ({2, 3} : Finset (Fin 6))
      ∧ degK ceEnds D' 3 = 1 ∧ #({0, 9} : Finset (Fin 10)) < #D'
      ∧ ∃ P, P ⊆ ({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))
          ∧ sources ceEnds P = ({0, 3} : Finset (Fin 6))
          ∧ Disjoint P D' ∧ connK ceEnds P 0 3
          ∧ connK ceEnds
              ((({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))) \ D') 0 3 := by
  refine ⟨({1, 2, 3} : Finset (Fin 10)), ceEnds_D123_subset, ceEnds_D123_sources, ceEnds_D123_gDeg1,
    ceEnds_D123_notMinCard, ({0} : Finset (Fin 10)), ?_, ceEnds_P0_sources, by decide,
    ceEnds_P0_conn, ?_⟩
  · rw [show (({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10)))
          = ({0, 1, 2, 3, 4, 9} : Finset (Fin 10)) from by decide]; decide
  · exact mng_connK_of_disjoint ceEnds
      (by rw [show (({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10)))
            = ({0, 1, 2, 3, 4, 9} : Finset (Fin 10)) from by decide]; decide)
      (by decide) ceEnds_P0_conn









theorem gc71_witness_gc66 :
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc69b_removalSurvival_of_ogSurvival gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) gc69b_witness_ogSurvival









theorem gc71_status :
    
    (¬ gc70b_OGConnAvoidingD ceEnds ({4} : Finset (Fin 10)) 0 1 2 3)
    ∧ (¬ gc69b_OGSurvival ceEnds ({4} : Finset (Fin 10)) 0 1 2 3)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W),
        o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
            gc66_GDeg1RemovalSurvival ends K o x y g) →
        gc39_ThreeColouringCountIneq ends o x y g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W),
        o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
            gc71_TwoCommodityLeaf ends K o x y g) →
        gc39_ThreeColouringCountIneq ends o x y g)
    ∧ 
    (∃ D', D' ⊆ univ \ ({4} : Finset (Fin 10)) ∧ sources ceEnds D' = ({2, 3} : Finset (Fin 6))
      ∧ degK ceEnds D' 3 = 1 ∧ #({0, 9} : Finset (Fin 10)) < #D'
      ∧ ∃ P, P ⊆ ({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))
          ∧ sources ceEnds P = ({0, 3} : Finset (Fin 6))
          ∧ Disjoint P D' ∧ connK ceEnds P 0 3
          ∧ connK ceEnds
              ((({4} : Finset (Fin 10)) ∪ ({0, 1, 2, 3, 9} : Finset (Fin 10))) \ D') 0 3)
    ∧ 
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨gc71_minCardResidue_false,
    gc71_ogSurvival_false,
    fun ends hnd o x y g hox hoy hog hxy hxg hyg huniv h =>
      gc71_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv h,
    fun ends hnd o x y g hox hoy hog hxy hxg hyg huniv h =>
      gc71_countIneq_of_twoCommodityLeaf ends hnd hox hoy hog hxy hxg hyg huniv h,
    gc71_ce_gDeg1_witness,
    gc71_witness_gc66⟩

end StatMech.Walls
