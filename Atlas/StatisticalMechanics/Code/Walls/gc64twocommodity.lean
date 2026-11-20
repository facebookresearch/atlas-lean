/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































































import Mathlib
import Code.Walls.gc63reroute
import Code.Walls.menger_core

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















def gc64_SharedSinkFixedD (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g





theorem gc64_disjointConnector_of_fixedD (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc64_SharedSinkFixedD ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hcut⟩ := h
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  refine ⟨(K ∪ L) \ D, Finset.sdiff_subset, ?_, hcut L hL⟩
  rw [Finset.disjoint_left]
  intro i hi
  exact (Finset.mem_sdiff.1 hi).2





theorem gc64_sharedSinkFixedD_of_disjointConnector (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc57_DisjointConnector ends K o x y g) :
    gc64_SharedSinkFixedD ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hconn⟩ := h
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  obtain ⟨P, hPG, hPD, hPconn⟩ := hconn L hL
  exact gc57_connK_of_disjoint_connector ends hPG hPD hPconn



theorem gc64_sharedSinkFixedD_iff_disjointConnector (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W} :
    gc64_SharedSinkFixedD ends K o x y g ↔ gc57_DisjointConnector ends K o x y g :=
  ⟨gc64_disjointConnector_of_fixedD ends K, gc64_sharedSinkFixedD_of_disjointConnector ends K⟩












theorem gc64_two_disjoint_from_g (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {g a : W} (hne : g ≠ a) (hga : connK ends G g a)
    (hga2 : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({g, a} : Finset W) →
        connK ends (G \ P₁) g a) :
    ∃ P₁ P₂ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ Disjoint P₁ P₂ ∧
      sources ends P₁ = ({g, a} : Finset W) ∧ sources ends P₂ = ({g, a} : Finset W) ∧
      connK ends P₁ g a ∧ connK ends P₂ g a :=
  mng_two_disjoint_connectors ends hnd hne hga hga2





theorem gc64_relative2_survives (ends : ι → Sym2 W) {G P₁ P₂ D : Finset ι}
    (hP₂G : P₂ ⊆ G) (hdisj : Disjoint P₁ P₂) (hDP₁ : D ⊆ P₁) {x g : W}
    (hP₂c : connK ends P₂ x g) :
    connK ends (G \ D) x g := by
  have hP₂D : Disjoint P₂ D := Finset.disjoint_of_subset_right hDP₁ hdisj.symm
  exact mng_connK_of_disjoint ends hP₂G hP₂D hP₂c













theorem gc64_disjointConnector_of_commonRel2 (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hxg : x ≠ g)
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hrel2 : ∀ L ∈ gc51_LblockSet ends K o x g,
        ∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ D ∩ (K ∪ L) ⊆ P₁ ∧
          sources ends P₁ = ({x, g} : Finset W) ∧ connK ends ((K ∪ L) \ P₁) x g) :
    gc64_SharedSinkFixedD ends K o x y g := by
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  obtain ⟨P₁, hP₁G, hDcap, hP₁src, hP₁surv⟩ := hrel2 L hL
  
  have hP₁conn : connK ends P₁ x g := by
    apply path_exists ends P₁ (fun i _ => hnd i) x g
    · rw [← mem_sources, hP₁src]; simp
    · intro z hz; rw [← mem_sources, hP₁src] at hz; simpa using hz
    · exact hxg
  
  
  
  obtain ⟨P₂, hP₂GP, hP₂src⟩ := exists_conn_set ends ((K ∪ L) \ P₁) hP₁surv hxg
  have hP₂G : P₂ ⊆ K ∪ L := fun i hi => (Finset.mem_sdiff.1 (hP₂GP hi)).1
  have hdisj : Disjoint P₁ P₂ := by
    rw [Finset.disjoint_right]
    intro i hi
    exact (Finset.mem_sdiff.1 (hP₂GP hi)).2
  have hP₂conn : connK ends P₂ x g := by
    apply path_exists ends P₂ (fun i _ => hnd i) x g
    · rw [← mem_sources, hP₂src]; simp
    · intro z hz; rw [← mem_sources, hP₂src] at hz; simpa using hz
    · exact hxg
  
  have hP₂cap : Disjoint P₂ (D ∩ (K ∪ L)) :=
    Finset.disjoint_of_subset_right hDcap hdisj.symm
  have hsurv : connK ends ((K ∪ L) \ (D ∩ (K ∪ L))) x g :=
    mng_connK_of_disjoint ends hP₂G hP₂cap hP₂conn
  have heq : (K ∪ L) \ (D ∩ (K ∪ L)) = (K ∪ L) \ D := by
    ext j
    simp only [Finset.mem_sdiff, Finset.mem_inter]
    constructor
    · rintro ⟨hj, hnot⟩; exact ⟨hj, fun hjD => hnot ⟨hjD, hj⟩⟩
    · rintro ⟨hj, hnot⟩; exact ⟨hj, fun ⟨hjD, _⟩ => hnot hjD⟩
  rwa [heq] at hsurv







theorem gc64_countIneq_of_sharedSinkFixedD (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc64_SharedSinkFixedD ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg hyg huniv
    (fun K hK => gc64_disjointConnector_of_fixedD ends K (h K hK))






theorem gc64_sharedSinkFixedD_of_disjoint (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
    gc64_SharedSinkFixedD ends K o x y g := by
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  have hLmem := hL
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨_, _, hgate⟩ := hL
  have hKD : Disjoint K D := by
    rw [Finset.disjoint_left]
    intro i hiK hiD
    exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK
  have heq : (K ∪ L) \ D = K ∪ L := by
    rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_union_left]
    exact ⟨hKD, hdisj L hLmem⟩
  rw [heq]; exact hgate




theorem gc64_sharedSinkFixedD_of_gDegOne (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hg1 : degK ends (univ : Finset ι) g = 1) :
    gc64_SharedSinkFixedD ends K o x y g := by
  obtain ⟨D, hDV, hDsrc⟩ := gc53_exists_fixedPath ends hnd K hoy hog hxy hxg hyg huniv hKsrc
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  rw [gc60_lblockSet_empty_of_gDegOne ends K (y := y) hog hxg hKsrc hg1] at hL
  exact absurd hL (Finset.notMem_empty L)


theorem gc64_disjointConnector_of_gDegOne' (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hg1 : degK ends (univ : Finset ι) g = 1) :
    gc57_DisjointConnector ends K o x y g :=
  gc64_disjointConnector_of_fixedD ends K
    (gc64_sharedSinkFixedD_of_gDegOne ends hnd K hoy hog hxy hxg hyg huniv hKsrc hg1)

end Abstract

open Classical








theorem gc64_witness_sharedSinkFixedD_K13 :
    gc64_SharedSinkFixedD gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc64_sharedSinkFixedD_of_disjoint (D := ({0, 2} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K13, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _


theorem gc64_witness_sharedSinkFixedD_K23 :
    gc64_SharedSinkFixedD gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc64_sharedSinkFixedD_of_disjoint (D := ({0, 1} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K23, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _



theorem gc64_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc55_cosetGateDom_of_removalSurvival
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc57_removalSurvival_of_disjointConnector gc49_witnessEnds _
      (gc64_disjointConnector_of_fixedD gc49_witnessEnds _ gc64_witness_sharedSinkFixedD_K13)
  · exact gc57_removalSurvival_of_disjointConnector gc49_witnessEnds _
      (gc64_disjointConnector_of_fixedD gc49_witnessEnds _ gc64_witness_sharedSinkFixedD_K23)










theorem gc64_refut_sharedSinkFixedD :
    gc64_SharedSinkFixedD gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 :=
  gc64_sharedSinkFixedD_of_disjointConnector gc63b_refutEnds ({0} : Finset (Fin 7))
    gc63b_refut_disjointConnector



theorem gc64_refut_sharedSink_beats_reroute :
    (¬ gc59_RerouteConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3)
    ∧ gc64_SharedSinkFixedD gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 :=
  ⟨gc63b_rerouteConnector_false, gc64_refut_sharedSinkFixedD⟩







theorem gc64_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W),
      gc64_SharedSinkFixedD ends K o x y g ↔ gc57_DisjointConnector ends K o x y g)
    ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3
    ∧ (¬ gc59_RerouteConnector gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3)
    ∧ gc64_SharedSinkFixedD gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 :=
  ⟨fun ends K o x y g => gc64_sharedSinkFixedD_iff_disjointConnector ends K,
    gc64_witness_cosetGateDom,
    gc63b_rerouteConnector_false,
    gc64_refut_sharedSinkFixedD⟩

end StatMech.Walls
