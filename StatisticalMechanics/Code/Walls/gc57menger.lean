/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/







































































































import Mathlib
import Code.Walls.gc56pathremoval

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
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]







theorem gc57_graph_sdiff (K L D : Finset ι) (hKD : Disjoint K D) :
    (K ∪ L) \ D = K ∪ (L \ D) := by
  ext j
  simp only [Finset.mem_sdiff, Finset.mem_union]
  rw [Finset.disjoint_left] at hKD
  constructor
  · rintro ⟨hj | hj, hnot⟩
    · exact Or.inl hj
    · exact Or.inr ⟨hj, hnot⟩
  · rintro (hj | ⟨hjL, hjD⟩)
    · exact ⟨Or.inl hj, fun hd => hKD hj hd⟩
    · exact ⟨Or.inr hjL, hjD⟩









theorem gc57_connK_of_disjoint_connector (ends : ι → Sym2 W) {P G D : Finset ι}
    (hPG : P ⊆ G) (hPD : Disjoint P D) {a b : W} (hab : connK ends P a b) :
    connK ends (G \ D) a b := by
  have hsub : P ⊆ G \ D := by
    intro i hi
    rw [Finset.mem_sdiff]
    exact ⟨hPG hi, Finset.disjoint_left.1 hPD hi⟩
  exact gc51_connK_mono ends hsub hab














def gc57_DisjointConnector (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g,
          ∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ connK ends P x g







theorem gc57_removalSurvival_of_disjointConnector (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc57_DisjointConnector ends K o x y g) :
    gc55_RemovalSurvival ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hconn⟩ := h
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  
  have hKD : Disjoint K D := by
    rw [Finset.disjoint_left]
    intro i hiK hiD
    exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK
  have hGE : (K ∪ L) \ D = K ∪ (L \ D) := gc57_graph_sdiff K L D hKD
  obtain ⟨P, hPG, hPD, hPconn⟩ := hconn L hL
  have := gc57_connK_of_disjoint_connector ends hPG hPD hPconn
  rwa [hGE] at this







theorem gc57_disjointConnector_of_removalSurvival (ends : ι → Sym2 W) (K : Finset ι) {L D : Finset ι}
    (hKD : Disjoint K D) {x g : W} (hrs : connK ends (K ∪ (L \ D)) x g) :
    ∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ connK ends P x g := by
  refine ⟨K ∪ (L \ D), ?_, ?_, hrs⟩
  · exact Finset.union_subset_union_right (Finset.sdiff_subset)
  · rw [Finset.disjoint_union_left]
    exact ⟨hKD, Finset.disjoint_left.2 (fun i hi => (Finset.mem_sdiff.1 hi).2)⟩





theorem gc57_disjointConnector_iff_removalSurvival (ends : ι → Sym2 W) (K : Finset ι) {L D : Finset ι}
    (hKD : Disjoint K D) {x g : W} :
    (∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ connK ends P x g) ↔ connK ends (K ∪ (L \ D)) x g := by
  constructor
  · rintro ⟨P, hPG, hPD, hPconn⟩
    have := gc57_connK_of_disjoint_connector ends hPG hPD hPconn
    rwa [gc57_graph_sdiff K L D hKD] at this
  · intro hrs
    exact gc57_disjointConnector_of_removalSurvival ends K hKD hrs





theorem gc57_disjointConnector_iff_removalSurvival_residue (ends : ι → Sym2 W) (K : Finset ι)
    {o x y g : W} :
    gc57_DisjointConnector ends K o x y g ↔ gc55_RemovalSurvival ends K o x y g := by
  constructor
  · exact gc57_removalSurvival_of_disjointConnector ends K
  · rintro ⟨D, hDV, hDsrc, hrs⟩
    have hKD : Disjoint K D := by
      rw [Finset.disjoint_left]
      intro i hiK hiD
      exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK
    refine ⟨D, hDV, hDsrc, ?_⟩
    intro L hL
    exact (gc57_disjointConnector_iff_removalSurvival ends K hKD).2 (hrs L hL)







theorem gc57_countIneq_of_disjointConnector (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc57_DisjointConnector ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc55_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv
    (fun K hK => gc57_removalSurvival_of_disjointConnector ends K (h K hK))







theorem gc57_disjointConnector_of_disjoint (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
    gc57_DisjointConnector ends K o x y g := by
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  have hLmem := hL
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨_, _, hgate⟩ := hL
  have hKD : Disjoint K D := by
    rw [Finset.disjoint_left]
    intro i hiK hiD
    exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK
  refine ⟨K ∪ L, Finset.Subset.refl _, ?_, hgate⟩
  rw [Finset.disjoint_union_left]
  exact ⟨hKD, hdisj L hLmem⟩






theorem gc57_disjointConnector_of_ygEdge (ends : ι → Sym2 W) (hnd : ∀ j : ι, ¬ (ends j).IsDiag)
    (K : Finset ι) {o x y g : W} (hyg : y ≠ g) {i : ι} (hiV : i ∈ univ \ K) (hi : ends i = s(y, g)) :
    gc57_DisjointConnector ends K o x y g :=
  (gc57_disjointConnector_iff_removalSurvival_residue ends K).2
    (gc55_removalSurvival_of_ygEdge ends hnd K hyg hiV hi)

end Abstract

open Classical










theorem gc57_witness_disjointConnector_K13 :
    gc57_DisjointConnector gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc57_disjointConnector_of_disjoint (D := ({0, 2} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K13, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _


theorem gc57_witness_disjointConnector_K23 :
    gc57_DisjointConnector gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc57_disjointConnector_of_disjoint (D := ({0, 1} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K23, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _



theorem gc57_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc55_cosetGateDom_of_removalSurvival
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc57_removalSurvival_of_disjointConnector gc49_witnessEnds _ gc57_witness_disjointConnector_K13
  · exact gc57_removalSurvival_of_disjointConnector gc49_witnessEnds _ gc57_witness_disjointConnector_K23



theorem gc57_witness_perKCount : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc53_perKCount_of_cosetGateDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc49_witnessEnds_univ_sources gc57_witness_cosetGateDom



























noncomputable def gc57_refEnds : Fin 7 → Sym2 (Fin 5) :=
  ![s(1, 3), s(2, 4), s(3, 4), s(1, 2), s(0, 3), s(0, 2), s(0, 1)]


theorem gc57_refEnds_univ_sources :
    sources gc57_refEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 5)) := by decide


theorem gc57_refEnds_K_sources :
    sources gc57_refEnds ({6} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5)) := by decide


theorem gc57_refEnds_D_sources :
    sources gc57_refEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
    ∧ sources gc57_refEnds ({1, 2} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) := by
  refine ⟨by decide, by decide⟩


theorem gc57_ref_base_lex_eq :
    (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({0, 3} : Finset (Fin 7))))
      = ({1, 2, 6} : Finset (Fin 7)) := by decide


theorem gc57_ref_base_wk_eq :
    (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({1, 2} : Finset (Fin 7))))
      = ({0, 3, 6} : Finset (Fin 7)) := by decide



theorem gc57_ref_wk_survives :
    connK gc57_refEnds ({0, 3, 6} : Finset (Fin 7)) 1 3 :=
  Relation.ReflTransGen.single ⟨0, by decide, by decide, by decide, by decide⟩





theorem gc57_ref_lex_fails :
    ¬ connK gc57_refEnds ({1, 2, 6} : Finset (Fin 7)) 1 3 := by
  intro h
  have inv : ∀ w : Fin 5, connK gc57_refEnds ({1, 2, 6} : Finset (Fin 7)) 1 w →
      (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
      rcases ih with rfl | rfl <;>
        (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)








theorem gc57_lexMinD_refuted :
    sources gc57_refEnds ({6} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 5))
    ∧ sources gc57_refEnds ({0, 3} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
    ∧ sources gc57_refEnds ({1, 2} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5))
    ∧ ¬ connK gc57_refEnds
        (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({0, 3} : Finset (Fin 7)))) 1 3
    ∧ connK gc57_refEnds
        (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({1, 2} : Finset (Fin 7)))) 1 3 := by
  refine ⟨gc57_refEnds_K_sources, by decide, by decide, ?_, ?_⟩
  · rw [gc57_ref_base_lex_eq]; exact gc57_ref_lex_fails
  · rw [gc57_ref_base_wk_eq]; exact gc57_ref_wk_survives





























theorem gc57_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W),
      gc57_DisjointConnector ends K o x y g ↔ gc55_RemovalSurvival ends K o x y g)
    ∧ (¬ connK gc57_refEnds
        (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({0, 3} : Finset (Fin 7)))) 1 3)
    ∧ (connK gc57_refEnds
        (({6} : Finset (Fin 7)) ∪ (({0, 1, 2, 3} : Finset (Fin 7)) \ ({1, 2} : Finset (Fin 7)))) 1 3)
    ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3
    ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  ⟨fun ends K o x y g => gc57_disjointConnector_iff_removalSurvival_residue ends K,
    (by rw [gc57_ref_base_lex_eq]; exact gc57_ref_lex_fails),
    (by rw [gc57_ref_base_wk_eq]; exact gc57_ref_wk_survives),
    gc57_witness_cosetGateDom, gc57_witness_perKCount⟩

end StatMech.Walls
