/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Walls.gc54cosetgate

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












theorem gc55_reroute (ends : ι → Sym2 W) (K' : Finset ι) (i : ι) {p q : W}
    (hi : i ∈ K') (hpq : ends i = s(p, q)) (hconn : connK ends (K' \ {i}) p q)
    {a b : W} (hab : connK ends K' a b) :
    connK ends (K' \ {i}) a b := by
  induction hab with
  | refl => exact Relation.ReflTransGen.refl
  | @tail c d _ hstep ih =>
    refine ih.trans ?_
    obtain ⟨j, hj, hc, hd, hcd⟩ := hstep
    by_cases hji : j = i
    · subst hji
      rw [hpq] at hc hd
      simp only [Sym2.mem_iff] at hc hd
      rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
      · exact absurd rfl hcd
      · exact hconn
      · exact connK_symm ends _ hconn
      · exact absurd rfl hcd
    · exact Relation.ReflTransGen.single ⟨j, Finset.mem_sdiff.2 ⟨hj, by simp [hji]⟩, hc, hd, hcd⟩



theorem gc55_sources_singleton (ends : ι → Sym2 W) (i : ι) {y g : W} (hyg : y ≠ g)
    (hi : ends i = s(y, g)) : sources ends ({i} : Finset ι) = ({y, g} : Finset W) := by
  ext v
  rw [mem_sources]
  simp only [degK, Finset.filter_singleton]
  rw [Finset.mem_insert, Finset.mem_singleton]
  by_cases hvi : v ∈ ends i
  · rw [if_pos hvi, Finset.card_singleton]
    rw [hi] at hvi
    simp only [Sym2.mem_iff] at hvi
    exact ⟨fun _ => by tauto, fun _ => ⟨0, rfl⟩⟩
  · rw [if_neg hvi, Finset.card_empty]
    rw [hi] at hvi
    simp only [Sym2.mem_iff, not_or] at hvi
    exact ⟨fun h => absurd h (by decide), by rintro (rfl | rfl) <;> tauto⟩






theorem gc55_yg_conn_of_removed_edge (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (L : Finset ι) (i : ι) {y g : W} (hyg : y ≠ g) (hiL : i ∈ L)
    (hLsrc : sources ends L = (∅ : Finset W)) (hi : ends i = s(y, g)) :
    connK ends (L \ {i}) y g := by
  have hsd : L \ {i} = L ∆ {i} := by rw [symmDiff_of_ge (by simpa using hiL)]
  have hsrc : sources ends (L \ {i}) = ({y, g} : Finset W) := by
    rw [hsd, sources_symmDiff, hLsrc, gc55_sources_singleton ends i hyg hi]; simp
  apply path_exists ends (L \ {i}) (fun j _ => hnd j) y g
  · rw [← mem_sources, hsrc]; simp
  · intro z hz; rw [← mem_sources, hsrc] at hz; simpa using hz
  · exact hyg













theorem gc55_singleEdge_removal_survival (ends : ι → Sym2 W) (hnd : ∀ j : ι, ¬ (ends j).IsDiag)
    (K : Finset ι) {o x y g : W} (hyg : y ≠ g) {i : ι} (hiV : i ∈ univ \ K) (hi : ends i = s(y, g))
    {L : Finset ι} (hL : L ∈ gc51_LblockSet ends K o x g) :
    connK ends (K ∪ (L \ {i})) x g := by
  have hiK : i ∉ K := (Finset.mem_sdiff.1 hiV).2
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨hLV, hLsrc, hgate⟩ := hL
  by_cases hiL : i ∈ L
  · 
    have hygL : connK ends (L \ {i}) y g :=
      gc55_yg_conn_of_removed_edge ends hnd L i hyg hiL hLsrc hi
    
    have hcut : (K ∪ L) \ {i} = K ∪ (L \ {i}) := by
      ext j
      simp only [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro ⟨hj | hj, hji⟩
        · exact Or.inl hj
        · exact Or.inr ⟨hj, hji⟩
      · rintro (hj | ⟨hj, hji⟩)
        · exact ⟨Or.inl hj, fun h => hiK (h ▸ hj)⟩
        · exact ⟨Or.inr hj, hji⟩
    
    have hygcut : connK ends ((K ∪ L) \ {i}) y g := by
      rw [hcut]; exact gc51_connK_mono ends Finset.subset_union_right hygL
    have hiKL : i ∈ K ∪ L := Finset.mem_union_right _ hiL
    have := gc55_reroute ends (K ∪ L) i hiKL hi hygcut hgate
    rwa [hcut] at this
  · 
    rw [Finset.sdiff_eq_self_of_disjoint (by simp [hiL])]
    exact hgate










theorem gc55_gate_removal_to_symmDiff (ends : ι → Sym2 W) (K : Finset ι) {L D : Finset ι}
    {x g : W} (hgate : connK ends (K ∪ (L \ D)) x g) :
    connK ends (K ∪ (L ∆ D)) x g :=
  gc51_connK_mono ends (Finset.union_subset_union_right symmDiff_subset_sdiff) hgate

















def gc55_RemovalSurvival (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g, connK ends (K ∪ (L \ D)) x g





theorem gc55_removalSurvival_of_disjoint (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hdisj : ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D) :
    gc55_RemovalSurvival ends K o x y g := by
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  have hLmem := hL
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨_, _, hgate⟩ := hL
  rwa [Finset.sdiff_eq_self_of_disjoint (hdisj L hLmem)]










theorem gc55_removalSurvival_of_ygEdge (ends : ι → Sym2 W) (hnd : ∀ j : ι, ¬ (ends j).IsDiag)
    (K : Finset ι) {o x y g : W} (hyg : y ≠ g) {i : ι} (hiV : i ∈ univ \ K) (hi : ends i = s(y, g)) :
    gc55_RemovalSurvival ends K o x y g := by
  refine ⟨{i}, ?_, ?_, ?_⟩
  · simpa using hiV
  · exact gc55_sources_singleton ends i hyg hi
  · intro L hL
    exact gc55_singleEdge_removal_survival ends hnd K hyg hiV hi hL













theorem gc55_gateShiftInjection_of_removalSurvival (ends : ι → Sym2 W) (K P₀ : Finset ι) {o x y g : W}
    (hP₀V : P₀ ⊆ univ \ K) (hP₀src : sources ends P₀ = ({y, g} : Finset W))
    (h : gc55_RemovalSurvival ends K o x y g) :
    gc54_GateShiftInjection ends K P₀ o x g := by
  obtain ⟨D, hDV, hDsrc, hsurv⟩ := h
  refine ⟨D ∆ P₀, ?_, ?_, ?_⟩
  · 
    intro i hi
    rw [Finset.mem_symmDiff] at hi
    rcases hi with ⟨h, _⟩ | ⟨h, _⟩
    · exact hDV h
    · exact hP₀V h
  · 
    rw [sources_symmDiff, hDsrc, hP₀src, symmDiff_self]; rfl
  · 
    intro L hL
    have hkey : (L ∆ (D ∆ P₀)) ∆ P₀ = L ∆ D := by
      rw [symmDiff_assoc, symmDiff_symmDiff_cancel_right]
    rw [hkey]
    exact gc55_gate_removal_to_symmDiff ends K (hsurv L hL)





theorem gc55_cosetGateDom_of_removalSurvival (ends : ι → Sym2 W) {o x y g : W}
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc55_RemovalSurvival ends K o x y g) :
    gc53_CosetGateDom ends o x y g := by
  apply gc54_cosetGateDom_of_gateShiftInjection
  intro K hK P₀ hP₀sub hP₀src
  exact gc55_gateShiftInjection_of_removalSurvival ends K P₀ hP₀sub hP₀src (h K hK)




theorem gc55_countIneq_of_removalSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc55_RemovalSurvival ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc53_countIneq_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv
    (gc55_cosetGateDom_of_removalSurvival ends h)

end Abstract

open Classical













theorem gc55_witness_removalSurvival_K13 :
    gc55_RemovalSurvival gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc55_removalSurvival_of_disjoint (D := ({0, 2} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K13, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _


theorem gc55_witness_removalSurvival_K23 :
    gc55_RemovalSurvival gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc55_removalSurvival_of_disjoint (D := ({0, 1} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) from by decide]
  · decide
  · intro L hL
    rw [gc51_witness_LblockSet_K23, Finset.mem_singleton] at hL
    subst hL
    exact Finset.disjoint_empty_left _





theorem gc55_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc55_cosetGateDom_of_removalSurvival
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc55_witness_removalSurvival_K13
  · exact gc55_witness_removalSurvival_K23




theorem gc55_witness_perKCount : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc53_perKCount_of_cosetGateDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc49_witnessEnds_univ_sources gc55_witness_cosetGateDom



















theorem gc55_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K P₀ : Finset ι) (o x y g : W),
      P₀ ⊆ univ \ K → sources ends P₀ = ({y, g} : Finset W) →
        gc55_RemovalSurvival ends K o x y g → gc54_GateShiftInjection ends K P₀ o x g)
    ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3
    ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  ⟨fun ends K P₀ o x y g hP hPs h =>
      gc55_gateShiftInjection_of_removalSurvival ends K P₀ hP hPs h,
    gc55_witness_cosetGateDom, gc55_witness_perKCount⟩

end StatMech.Walls
