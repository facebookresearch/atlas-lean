/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



























































































import Mathlib
import Code.Walls.gc61parallelg

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












theorem gc62_residual_gDegGe3 (ends : ι → Sym2 W) {o x y g : W}
    (hog : o ≠ g) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hne1 : degK ends (univ : Finset ι) g ≠ 1) :
    3 ≤ degK ends (univ : Finset ι) g := by
  rcases gc60_gDeg_dichotomy ends hog hxg hyg huniv with h1 | h3
  · exact absurd h1 hne1
  · exact h3

end Abstract

open Classical
















noncomputable def gc62_refutEnds : Fin 7 → Sym2 (Fin 4) :=
  ![s(0, 1), s(1, 2), s(1, 2), s(1, 2), s(1, 3), s(2, 3), s(2, 3)]


theorem gc62_refut_univ_sources :
    sources gc62_refutEnds (univ : Finset (Fin 7)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc62_refut_K_sources :
    sources gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) = ({0, 1} : Finset (Fin 4)) := by decide



theorem gc62_refut_gDeg :
    degK gc62_refutEnds (univ : Finset (Fin 7)) (3 : Fin 4) = 3 := by decide


theorem gc62_refut_loopless : ∀ i : Fin 7, ¬ (gc62_refutEnds i).IsDiag := by decide




theorem gc62_conn_12 :
    connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 2} : Finset (Fin 7))) 1 3 :=
  (Relation.ReflTransGen.single (b := (2 : Fin 4)) ⟨1, by decide, by decide, by decide, by decide⟩).tail
    ⟨5, by decide, by decide, by decide, by decide⟩


theorem gc62_conn_13 :
    connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 3} : Finset (Fin 7))) 1 3 :=
  (Relation.ReflTransGen.single (b := (2 : Fin 4)) ⟨1, by decide, by decide, by decide, by decide⟩).tail
    ⟨5, by decide, by decide, by decide, by decide⟩


theorem gc62_conn_23 :
    connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ ({2, 3} : Finset (Fin 7))) 1 3 :=
  (Relation.ReflTransGen.single (b := (2 : Fin 4)) ⟨2, by decide, by decide, by decide, by decide⟩).tail
    ⟨5, by decide, by decide, by decide, by decide⟩



theorem gc62_not_conn_empty :
    ¬ connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ (∅ : Finset (Fin 7))) 1 3 := by
  rw [Finset.union_empty]
  intro h
  have inv : ∀ w : Fin 4, connK gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 1 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)



theorem gc62_refut_LblockSet :
    gc51_LblockSet gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 3
      = ({{1, 2}, {1, 3}, {2, 3}} : Finset (Finset (Fin 7))) := by
  rw [gc51_LblockSet]
  have hV : (univ : Finset (Fin 7)) \ ({0, 5, 6} : Finset (Fin 7)) = ({1, 2, 3, 4} : Finset (Fin 7)) := by
    decide
  rw [hV]
  have hset : ({1, 2, 3, 4} : Finset (Fin 7)).powerset.filter
      (fun L => sources gc62_refutEnds L = (∅ : Finset (Fin 4)))
      = ({∅, {1, 2}, {1, 3}, {2, 3}} : Finset (Finset (Fin 7))) := by decide
  rw [show ({1, 2, 3, 4} : Finset (Fin 7)).powerset.filter
        (fun L => sources gc62_refutEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ L) 1 3)
      = (({1, 2, 3, 4} : Finset (Fin 7)).powerset.filter
          (fun L => sources gc62_refutEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc62_refutEnds (({0, 5, 6} : Finset (Fin 7)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  ext L
  simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hLmem, hconn⟩
    rcases hLmem with rfl | rfl | rfl | rfl
    · exact absurd hconn gc62_not_conn_empty
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  · rintro (rfl | rfl | rfl)
    · exact ⟨by simp, gc62_conn_12⟩
    · exact ⟨by simp, gc62_conn_13⟩
    · exact ⟨by simp, gc62_conn_23⟩






theorem gc62_gIncident (i : Fin 7) (v : Fin 4) (hi : gc62_refutEnds i = s(v, 3)) (hv : v ≠ 3) :
    i = 4 ∨ i = 5 ∨ i = 6 := by
  fin_cases i <;> simp_all [gc62_refutEnds]











theorem gc62_parallelTwinPresent_false :
    ¬ gc61_ParallelTwinPresent gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3 := by
  rintro ⟨D, i, v, hDV, hDsrc, hi, hv, hL⟩
  have hi456 : i = 4 ∨ i = 5 ∨ i = 6 := gc62_gIncident i v hi hv
  have hDsub : D ⊆ ({1, 2, 3, 4} : Finset (Fin 7)) := by
    have hVeq : (univ : Finset (Fin 7)) \ ({0, 5, 6} : Finset (Fin 7)) = ({1, 2, 3, 4} : Finset (Fin 7)) := by
      decide
    rw [hVeq] at hDV; exact hDV
  
  have hmem : ∀ L : Finset (Fin 7),
      L = ({1, 2} : Finset (Fin 7)) ∨ L = ({1, 3} : Finset (Fin 7)) ∨ L = ({2, 3} : Finset (Fin 7)) →
      L ∈ gc51_LblockSet gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 3 := by
    intro L hLc; rw [gc62_refut_LblockSet]; rcases hLc with rfl | rfl | rfl <;> decide
  
  have key : ∀ L : Finset (Fin 7),
      L = ({1, 2} : Finset (Fin 7)) ∨ L = ({1, 3} : Finset (Fin 7)) ∨ L = ({2, 3} : Finset (Fin 7)) →
      D ∩ (({0, 5, 6} : Finset (Fin 7)) ∪ L) = ∅ := by
    intro L hLc
    obtain ⟨_, hdisj⟩ := hL L (hmem L hLc)
    rcases hdisj with ⟨hDinter, hiKL, _⟩ | hempty
    · exfalso
      have hiD : i ∈ D := by
        have hmemi : i ∈ D ∩ (({0, 5, 6} : Finset (Fin 7)) ∪ L) := by
          rw [hDinter]; exact Finset.mem_singleton_self i
        exact (Finset.mem_inter.1 hmemi).1
      have hiV : i ∈ ({1, 2, 3, 4} : Finset (Fin 7)) := hDsub hiD
      have hi4 : i = 4 := by
        rcases hi456 with h | h | h
        · exact h
        · subst h; revert hiV; decide
        · subst h; revert hiV; decide
      subst hi4
      rcases hLc with rfl | rfl | rfl <;> (revert hiKL; decide)
    · exact hempty
  have h12 := key ({1, 2} : Finset (Fin 7)) (Or.inl rfl)
  have h13 := key ({1, 3} : Finset (Fin 7)) (Or.inr (Or.inl rfl))
  
  have hn1 : (1 : Fin 7) ∉ D := by
    intro hc
    have hin : (1 : Fin 7) ∈ D ∩ (({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 2} : Finset (Fin 7))) :=
      Finset.mem_inter.2 ⟨hc, by decide⟩
    rw [h12] at hin; exact absurd hin (Finset.notMem_empty _)
  have hn2 : (2 : Fin 7) ∉ D := by
    intro hc
    have hin : (2 : Fin 7) ∈ D ∩ (({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 2} : Finset (Fin 7))) :=
      Finset.mem_inter.2 ⟨hc, by decide⟩
    rw [h12] at hin; exact absurd hin (Finset.notMem_empty _)
  have hn3 : (3 : Fin 7) ∉ D := by
    intro hc
    have hin : (3 : Fin 7) ∈ D ∩ (({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 3} : Finset (Fin 7))) :=
      Finset.mem_inter.2 ⟨hc, by decide⟩
    rw [h13] at hin; exact absurd hin (Finset.notMem_empty _)
  
  have hDsub4 : D ⊆ ({4} : Finset (Fin 7)) := by
    intro j hj
    have hjV := hDsub hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hjV ⊢
    rcases hjV with rfl | rfl | rfl | rfl
    · exact absurd hj hn1
    · exact absurd hj hn2
    · exact absurd hj hn3
    · rfl
  
  rcases Finset.subset_singleton_iff.1 hDsub4 with rfl | rfl
  · rw [show sources gc62_refutEnds (∅ : Finset (Fin 7)) = (∅ : Finset (Fin 4)) from by decide] at hDsrc
    exact absurd hDsrc (by decide)
  · rw [show sources gc62_refutEnds ({4} : Finset (Fin 7)) = ({1, 3} : Finset (Fin 4)) from by decide] at hDsrc
    exact absurd hDsrc (by decide)




theorem gc62_refut_not_gateInK :
    ¬ connK gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 1 3 := by
  intro h; exact gc62_not_conn_empty (by rw [Finset.union_empty]; exact h)


theorem gc62_refut_not_gDegOne :
    degK gc62_refutEnds (univ : Finset (Fin 7)) (3 : Fin 4) ≠ 1 := by
  rw [gc62_refut_gDeg]; decide



theorem gc62_refut_no_ygEdge :
    ¬ ∃ i, i ∈ (univ : Finset (Fin 7)) \ ({0, 5, 6} : Finset (Fin 7)) ∧ gc62_refutEnds i = s(2, 3) := by
  decide



theorem gc62_refut_in_residual :
    3 ≤ degK gc62_refutEnds (univ : Finset (Fin 7)) (3 : Fin 4) :=
  gc62_residual_gDegGe3 gc62_refutEnds (by decide) (by decide) (by decide)
    gc62_refut_univ_sources gc62_refut_not_gDegOne










theorem gc62_refut_D_sources :
    sources gc62_refutEnds ({1, 4} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 4)) := by decide



theorem gc62_reconn_12 :
    connK gc62_refutEnds ((({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 2} : Finset (Fin 7))) \ {1}) 1 2 := by
  have h : (({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 2} : Finset (Fin 7))) \ ({1} : Finset (Fin 7))
      = ({0, 2, 5, 6} : Finset (Fin 7)) := by decide
  rw [h]
  exact Relation.ReflTransGen.single ⟨2, by decide, by decide, by decide, by decide⟩



theorem gc62_reconn_13 :
    connK gc62_refutEnds ((({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 3} : Finset (Fin 7))) \ {1}) 1 2 := by
  have h : (({0, 5, 6} : Finset (Fin 7)) ∪ ({1, 3} : Finset (Fin 7))) \ ({1} : Finset (Fin 7))
      = ({0, 3, 5, 6} : Finset (Fin 7)) := by decide
  rw [h]
  exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩






theorem gc62_refut_rerouteConnector :
    gc59_RerouteConnector gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3 := by
  refine ⟨({1, 4} : Finset (Fin 7)), ?_, gc62_refut_D_sources, ?_⟩
  · rw [show (univ : Finset (Fin 7)) \ ({0, 5, 6} : Finset (Fin 7)) = ({1, 2, 3, 4} : Finset (Fin 7)) from by decide]
    decide
  · intro L hL
    rw [gc62_refut_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · 
      refine ⟨[1], by decide, ⟨by decide, ⟨1, 2, by decide, gc62_reconn_12⟩, trivial⟩, gc62_conn_12⟩
    · 
      refine ⟨[1], by decide, ⟨by decide, ⟨1, 2, by decide, gc62_reconn_13⟩, trivial⟩, gc62_conn_13⟩
    · 
      refine ⟨[], by decide, trivial, gc62_conn_23⟩





theorem gc62_refut_disjointConnector :
    gc57_DisjointConnector gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3 :=
  gc59_disjointConnector_of_reroute gc62_refutEnds _ gc62_refut_rerouteConnector





























theorem gc62_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (o x y g : W), o ≠ g → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        degK ends (univ : Finset ι) g ≠ 1 → 3 ≤ degK ends (univ : Finset ι) g)
    ∧ 
    (¬ gc61_ParallelTwinPresent gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3)
    ∧ 
    (3 ≤ degK gc62_refutEnds (univ : Finset (Fin 7)) (3 : Fin 4)
      ∧ ¬ connK gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 1 3
      ∧ ¬ ∃ i, i ∈ (univ : Finset (Fin 7)) \ ({0, 5, 6} : Finset (Fin 7)) ∧ gc62_refutEnds i = s(2, 3))
    ∧ 
    gc57_DisjointConnector gc62_refutEnds ({0, 5, 6} : Finset (Fin 7)) 0 1 2 3 :=
  ⟨fun ends o x y g hog hxg hyg huniv hne1 => gc62_residual_gDegGe3 ends hog hxg hyg huniv hne1,
    gc62_parallelTwinPresent_false,
    ⟨gc62_refut_in_residual, gc62_refut_not_gateInK, gc62_refut_no_ygEdge⟩,
    gc62_refut_disjointConnector⟩

end StatMech.Walls
