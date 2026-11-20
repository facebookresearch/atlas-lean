/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































































import Mathlib
import Code.Walls.menger_core
import Code.Walls.gc60exhaustive

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
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm sources_symmDiff mem_sources
  path_exists exists_conn_set adjStep degK)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]










theorem gc61_connK_singleton (ends : ι → Sym2 W) {i : ι} {v g : W} (hvg : v ≠ g)
    (hi : ends i = s(v, g)) : connK ends ({i} : Finset ι) v g :=
  Relation.ReflTransGen.single
    ⟨i, Finset.mem_singleton_self i, by rw [hi]; exact Sym2.mem_mk_left v g,
      by rw [hi]; exact Sym2.mem_mk_right v g, hvg⟩



theorem gc61_connK_parallel (ends : ι → Sym2 W) {i j : ι} {v g : W} (hvg : v ≠ g)
    (hi : ends i = s(v, g)) : connK ends ({i, j} : Finset ι) v g :=
  mng_connK_mono ends (by intro k hk; simp only [Finset.mem_singleton] at hk; subst hk; simp)
    (gc61_connK_singleton ends hvg hi)



theorem gc61_sources_singleton (ends : ι → Sym2 W) (i : ι) {v g : W} (hvg : v ≠ g)
    (hi : ends i = s(v, g)) : sources ends ({i} : Finset ι) = ({v, g} : Finset W) := by
  ext x
  simp only [mem_sources, degK, Finset.filter_singleton, Finset.mem_insert, Finset.mem_singleton]
  by_cases hx : x ∈ ends i
  · rw [if_pos hx, Finset.card_singleton]
    have hxvg : x = v ∨ x = g := by
      rw [hi, Sym2.mem_iff] at hx; exact hx
    simp only [show Odd 1 from ⟨0, rfl⟩, true_iff]; exact hxvg
  · rw [if_neg hx, Finset.card_empty]
    have hxvg : ¬ (x = v ∨ x = g) := by
      rintro (rfl | rfl)
      · exact hx (by rw [hi]; exact Sym2.mem_mk_left x g)
      · exact hx (by rw [hi]; exact Sym2.mem_mk_right v x)
    simp only [show ¬ Odd 0 from by decide, false_iff]; exact hxvg










theorem gc61_relative2conn_of_parallel (ends : ι → Sym2 W) {i j : ι} {v g : W}
    (hij : i ≠ j) (hvg : v ≠ g) (hi : ends i = s(v, g)) (hj : ends j = s(v, g))
    (P₁ : Finset ι) (hP₁G : P₁ ⊆ ({i, j} : Finset ι))
    (hP₁src : sources ends P₁ = ({v, g} : Finset W)) :
    connK ends (({i, j} : Finset ι) \ P₁) v g := by
  
  have hgP₁ : Odd (degK ends P₁ g) := by
    rw [← mem_sources, hP₁src]; simp
  
  
  
  
  have hgi : g ∈ ends i := by rw [hi]; exact Sym2.mem_mk_right v g
  have hgj : g ∈ ends j := by rw [hj]; exact Sym2.mem_mk_right v g
  
  by_cases hiP : i ∈ P₁ <;> by_cases hjP : j ∈ P₁
  · 
    exfalso
    have hfilt : P₁.filter (fun k => g ∈ ends k) = {i, j} := by
      apply Finset.Subset.antisymm
      · intro k hk; rw [Finset.mem_filter] at hk
        have := hP₁G hk.1; simpa using this
      · intro k hk; simp only [Finset.mem_insert, Finset.mem_singleton] at hk
        rcases hk with rfl | rfl
        · exact Finset.mem_filter.2 ⟨hiP, hgi⟩
        · exact Finset.mem_filter.2 ⟨hjP, hgj⟩
    have : degK ends P₁ g = 2 := by
      rw [degK, hfilt, Finset.card_insert_of_notMem (by simp [hij]), Finset.card_singleton]
    rw [this] at hgP₁; exact (by decide : ¬ Odd 2) hgP₁
  · 
    have hjmem : j ∈ ({i, j} : Finset ι) \ P₁ := Finset.mem_sdiff.2 ⟨by simp, hjP⟩
    exact mng_connK_mono ends
      (by intro k hk; simp only [Finset.mem_singleton] at hk; subst hk; exact hjmem)
      (gc61_connK_singleton ends hvg hj)
  · 
    have himem : i ∈ ({i, j} : Finset ι) \ P₁ := Finset.mem_sdiff.2 ⟨by simp, hiP⟩
    exact mng_connK_mono ends
      (by intro k hk; simp only [Finset.mem_singleton] at hk; subst hk; exact himem)
      (gc61_connK_singleton ends hvg hi)
  · 
    exfalso
    have hfilt : P₁.filter (fun k => g ∈ ends k) = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro k hk; rw [Finset.mem_filter] at hk
      have := hP₁G hk.1; simp only [Finset.mem_insert, Finset.mem_singleton] at this
      rcases this with rfl | rfl
      · exact hiP hk.1
      · exact hjP hk.1
    have : degK ends P₁ g = 0 := by rw [degK, hfilt, Finset.card_empty]
    rw [this] at hgP₁; exact (by decide : ¬ Odd 0) hgP₁













theorem gc61_two_disjoint_of_parallel (ends : ι → Sym2 W) (hnd : ∀ k : ι, ¬ (ends k).IsDiag)
    {i j : ι} {v g : W} (hij : i ≠ j) (hvg : v ≠ g)
    (hi : ends i = s(v, g)) (hj : ends j = s(v, g)) :
    ∃ P₁ P₂ : Finset ι, P₁ ⊆ ({i, j} : Finset ι) ∧ P₂ ⊆ ({i, j} : Finset ι) ∧ Disjoint P₁ P₂ ∧
      sources ends P₁ = ({v, g} : Finset W) ∧ sources ends P₂ = ({v, g} : Finset W) ∧
      connK ends P₁ v g ∧ connK ends P₂ v g :=
  mng_two_disjoint_connectors ends hnd hvg (gc61_connK_parallel ends hvg hi)
    (fun P₁ hP₁G hP₁src => gc61_relative2conn_of_parallel ends hij hvg hi hj P₁ hP₁G hP₁src)













theorem gc61_parallel_reconnect (ends : ι → Sym2 W) {G : Finset ι} {i j : ι} {v g : W}
    (hij : i ≠ j) (hvg : v ≠ g) (hj : ends j = s(v, g)) (hjG : j ∈ G) :
    connK ends (G \ {i}) v g := by
  have hjmem : j ∈ G \ {i} := Finset.mem_sdiff.2 ⟨hjG, by simp [Ne.symm hij]⟩
  exact mng_connK_mono ends
    (by intro k hk; simp only [Finset.mem_singleton] at hk; subst hk; exact hjmem)
    (gc61_connK_singleton ends hvg hj)










def gc61_ParallelTwinPresent (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D i v, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ ends i = s(v, g) ∧ v ≠ g
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g,
          connK ends (K ∪ L) x g ∧
          ((D ∩ (K ∪ L) = {i} ∧ i ∈ K ∪ L ∧ connK ends ((K ∪ L) \ {i}) v g)
            ∨ D ∩ (K ∪ L) = ∅)







theorem gc61_rerouteConnector_of_parallelTwin (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc61_ParallelTwinPresent ends K o x y g) :
    gc59_RerouteConnector ends K o x y g := by
  obtain ⟨D, i, v, hDV, hDsrc, hi, hvg, hL⟩ := h
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hLmem
  obtain ⟨hgate, hcase⟩ := hL L hLmem
  rcases hcase with ⟨hDinter, hiKL, hreconn⟩ | hDempty
  · 
    refine ⟨[i], ?_, ?_, hgate⟩
    · simp [hDinter]
    · refine ⟨hiKL, ⟨v, g, hi, hreconn⟩, ?_⟩
      simp [gc59_Peelable]
  · 
    refine ⟨[], ?_, trivial, hgate⟩
    simp [hDempty]



theorem gc61_disjointConnector_of_parallelTwin (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc61_ParallelTwinPresent ends K o x y g) :
    gc57_DisjointConnector ends K o x y g :=
  gc59_disjointConnector_of_reroute ends K (gc61_rerouteConnector_of_parallelTwin ends K h)


















theorem gc61_disjointConnector_all (ends : ι → Sym2 W) (hnd : ∀ k : ι, ¬ (ends k).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hcov :
      (connK ends K x g)
      ∨ (degK ends (univ : Finset ι) g = 1)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc61_ParallelTwinPresent ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  rcases hcov with hxg | hg1 | hyge | hdisj | htwin
  · exact gc58_disjointConnector_of_gateInK_exists ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hxg
  · exact gc60_disjointConnector_of_gDegOne ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hg1
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inl hyge))
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inr hdisj))
  · exact gc61_disjointConnector_of_parallelTwin ends K htwin





theorem gc61_countIneq_of_cover (ends : ι → Sym2 W) (hnd : ∀ k : ι, ¬ (ends k).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      (connK ends K x g)
      ∨ (degK ends (univ : Finset ι) g = 1)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc61_ParallelTwinPresent ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg' hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc61_disjointConnector_all ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (hcov K hK)

end Abstract

open Classical

















noncomputable def gc61_gStar : Fin 3 → Sym2 (Fin 4) := ![s(0, 3), s(1, 3), s(2, 3)]


theorem gc61_gStar_univ_sources :
    sources gc61_gStar (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc61_gStar_gDeg : degK gc61_gStar (univ : Finset (Fin 3)) (3 : Fin 4) = 3 := by decide


theorem gc61_gStar_xg_conn : connK gc61_gStar (univ : Finset (Fin 3)) 1 3 :=
  Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩


theorem gc61_gStar_P1_sources :
    sources gc61_gStar ({1} : Finset (Fin 3)) = ({1, 3} : Finset (Fin 4)) := by decide


theorem gc61_gStar_delete_eq :
    (univ : Finset (Fin 3)) \ ({1} : Finset (Fin 3)) = ({0, 2} : Finset (Fin 3)) := by decide




theorem gc61_gStar_delete_disconn :
    ¬ connK gc61_gStar ({0, 2} : Finset (Fin 3)) 1 3 := by
  intro h
  have inv : ∀ w : Fin 4, connK gc61_gStar ({0, 2} : Finset (Fin 3)) 1 w → w = 1 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
      subst ih; fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide
  exact absurd (inv 3 h) (by decide)










theorem gc61_relative2conn_of_gDegGe3_false :
    ∃ (ends : Fin 3 → Sym2 (Fin 4)) (P₁ : Finset (Fin 3)),
      sources ends (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ 3 ≤ degK ends (univ : Finset (Fin 3)) (3 : Fin 4)
      ∧ connK ends (univ : Finset (Fin 3)) 1 3
      ∧ P₁ ⊆ (univ : Finset (Fin 3))
      ∧ sources ends P₁ = ({1, 3} : Finset (Fin 4))
      ∧ ¬ connK ends ((univ : Finset (Fin 3)) \ P₁) 1 3 := by
  refine ⟨gc61_gStar, {1}, gc61_gStar_univ_sources, by rw [gc61_gStar_gDeg], gc61_gStar_xg_conn,
    Finset.subset_univ _, gc61_gStar_P1_sources, ?_⟩
  rw [gc61_gStar_delete_eq]; exact gc61_gStar_delete_disconn





theorem gc61_gStar_rel2_x_g_fails :
    ¬ (∀ P₁ : Finset (Fin 3), P₁ ⊆ (univ : Finset (Fin 3)) →
        sources gc61_gStar P₁ = ({1, 3} : Finset (Fin 4)) →
        connK gc61_gStar ((univ : Finset (Fin 3)) \ P₁) 1 3) := by
  intro h
  have := h {1} (Finset.subset_univ _) gc61_gStar_P1_sources
  rw [gc61_gStar_delete_eq] at this
  exact gc61_gStar_delete_disconn this










noncomputable def gc61_parWit : Fin 2 → Sym2 (Fin 4) := ![s(0, 3), s(0, 3)]


theorem gc61_parWit_loopless : ∀ k : Fin 2, ¬ (gc61_parWit k).IsDiag := by decide





theorem gc61_parWit_two_disjoint :
    ∃ P₁ P₂ : Finset (Fin 2), P₁ ⊆ ({0, 1} : Finset (Fin 2)) ∧ P₂ ⊆ ({0, 1} : Finset (Fin 2)) ∧
      Disjoint P₁ P₂ ∧ sources gc61_parWit P₁ = ({0, 3} : Finset (Fin 4)) ∧
      sources gc61_parWit P₂ = ({0, 3} : Finset (Fin 4)) ∧
      connK gc61_parWit P₁ 0 3 ∧ connK gc61_parWit P₂ 0 3 :=
  gc61_two_disjoint_of_parallel gc61_parWit gc61_parWit_loopless (by decide) (by decide)
    (by decide) (by decide)








theorem gc61_witness_parallelTwin :
    gc61_ParallelTwinPresent gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine ⟨({1, 2} : Finset (Fin 5)), 2, 0, ?_, gc59_witnessEnds_D_sources, by decide, by decide, ?_⟩
  · rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
    decide
  · intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · 
      refine ⟨gc59_witness_conn_23, Or.inl ⟨by decide, by decide, ?_⟩⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) \ ({2} : Finset (Fin 5))
            = ({0, 3} : Finset (Fin 5)) from by decide]
      exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
    · 
      refine ⟨gc59_witness_conn_24, Or.inl ⟨by decide, by decide, ?_⟩⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) \ ({2} : Finset (Fin 5))
            = ({0, 4} : Finset (Fin 5)) from by decide]
      exact Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩
    · 
      exact ⟨gc59_witness_conn_34, Or.inr (by decide)⟩



theorem gc61_witness_disjointConnector :
    gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc61_disjointConnector_of_parallelTwin gc59_witnessEnds _ gc61_witness_parallelTwin





































theorem gc61_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (i j : ι) (v g : W), i ≠ j → v ≠ g →
        ends i = s(v, g) → ends j = s(v, g) →
        ∀ P₁ : Finset ι, P₁ ⊆ ({i, j} : Finset ι) →
          sources ends P₁ = ({v, g} : Finset W) → connK ends (({i, j} : Finset ι) \ P₁) v g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W),
        gc61_ParallelTwinPresent ends K o x y g → gc57_DisjointConnector ends K o x y g)
    ∧ 
    (∃ (ends : Fin 3 → Sym2 (Fin 4)) (P₁ : Finset (Fin 3)),
      3 ≤ degK ends (univ : Finset (Fin 3)) (3 : Fin 4)
      ∧ connK ends (univ : Finset (Fin 3)) 1 3
      ∧ sources ends P₁ = ({1, 3} : Finset (Fin 4))
      ∧ ¬ connK ends ((univ : Finset (Fin 3)) \ P₁) 1 3)
    ∧ 
    gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends i j v g hij hvg hi hj P₁ hP₁G hP₁src =>
      gc61_relative2conn_of_parallel ends hij hvg hi hj P₁ hP₁G hP₁src,
    fun ends K o x y g h => gc61_disjointConnector_of_parallelTwin ends K h,
    ⟨gc61_gStar, {1}, by rw [gc61_gStar_gDeg], gc61_gStar_xg_conn, gc61_gStar_P1_sources,
      by rw [gc61_gStar_delete_eq]; exact gc61_gStar_delete_disconn⟩,
    gc61_witness_disjointConnector⟩

end StatMech.Walls
