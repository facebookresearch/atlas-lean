/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





































































































import Mathlib
import Code.Walls.gc71cyclespace
import Code.Walls.menger_general

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








theorem gc72_trim_to_ogBoundary (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G D : Finset ι} {o g : W} (hog : o ≠ g)
    (hconn : connK ends (G \ D) o g) :
    ∃ P, P ⊆ G ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g := by
  obtain ⟨P', hP'sub, hP'src⟩ := exists_conn_set ends (G \ D) hconn hog
  refine ⟨P', hP'sub.trans Finset.sdiff_subset, hP'src, ?_, ?_⟩
  · 
    rw [Finset.disjoint_left]
    intro i hi
    exact (Finset.mem_sdiff.1 (hP'sub hi)).2
  · apply path_exists ends P' (fun i _ => hnd i) o g
    · rw [← mem_sources, hP'src]; simp
    · intro z hz; rw [← mem_sources, hP'src] at hz; simpa using hz
    · exact hog






theorem gc72_twoCommodityLeaf_of_removalSurvival (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc66_GDeg1RemovalSurvival ends K o x y g) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hD1, hsurv⟩ := h
  refine ⟨D, hDV, hDsrc, hD1, ?_⟩
  intro L hL
  
  have hxg' : connK ends ((K ∪ L) \ D) x g := hsurv L hL
  have hog' : connK ends ((K ∪ L) \ D) o g :=
    (gc68_xg_iff_og_survives ends hnd hox hKsrc hDV).1 hxg'
  
  exact gc72_trim_to_ogBoundary ends hnd hog hog'






theorem gc72_twoCommodityLeaf_iff_removalSurvival (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    gc71_TwoCommodityLeaf ends K o x y g ↔ gc66_GDeg1RemovalSurvival ends K o x y g :=
  ⟨gc71_gc66_of_twoCommodityLeaf ends hnd K hox hKsrc,
    gc72_twoCommodityLeaf_of_removalSurvival ends hnd K hox hog hKsrc⟩














theorem gc72_leafClause_iff_survives (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o g : W} (hog : o ≠ g) :
    (∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g)
      ↔ connK ends ((K ∪ L) \ D) o g := by
  constructor
  · rintro ⟨P, hPG, _, hPD, hPconn⟩
    exact mng_connK_of_disjoint ends hPG hPD hPconn
  · intro hconn
    exact gc72_trim_to_ogBoundary ends hnd hog hconn








theorem gc72_ogSurvives_of_relConn (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {o g : W} (hog : o ≠ g) (hconn : connK ends G o g)
    (hrel : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({o, g} : Finset W) →
        connK ends (G \ P₁) o g)
    {D : Finset ι}
    (hDsub : ∃ P₁ : Finset ι, P₁ ⊆ G ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁) :
    ∃ P, P ⊆ G ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g := by
  obtain ⟨P₁, hP₁G, hP₁src, hDP₁⟩ := hDsub
  have hrel' : connK ends (G \ P₁) o g := hrel P₁ hP₁G hP₁src
  obtain ⟨P₂, hP₂GP, hP₂src⟩ := exists_conn_set ends (G \ P₁) hrel' hog
  have hP₂G : P₂ ⊆ G := fun i hi => (Finset.mem_sdiff.1 (hP₂GP hi)).1
  have hP₂P₁ : Disjoint P₂ P₁ := by
    rw [Finset.disjoint_left]
    intro i hi
    exact (Finset.mem_sdiff.1 (hP₂GP hi)).2
  have hP₂D : Disjoint P₂ D := Finset.disjoint_of_subset_right hDP₁ hP₂P₁
  have hP₂conn : connK ends P₂ o g := mng_connK_of_sources ends hnd P₂ hog hP₂src
  exact ⟨P₂, hP₂G, hP₂src, hP₂D, hP₂conn⟩




theorem gc72_og_in_KL (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι)
    {o x g : W} (hox : o ≠ x) (hKsrc : sources ends K = ({o, x} : Finset W))
    {L : Finset ι} (hL : L ∈ gc51_LblockSet ends K o x g) :
    connK ends (K ∪ L) o g := by
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨_, _, hxg⟩ := hL
  have hoxK : connK ends K o x := by
    apply path_exists ends K (fun i _ => hnd i) o x
    · rw [← mem_sources, hKsrc]; simp
    · intro z hz; rw [← mem_sources, hKsrc] at hz; simpa using hz
    · exact hox
  exact (mng_connK_mono ends Finset.subset_union_left hoxK).trans hxg






theorem gc72_twoCommodityLeaf_of_relConn (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hrel : ∀ L ∈ gc51_LblockSet ends K o x g,
        (∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) →
            connK ends ((K ∪ L) \ P₁) o g)
          ∧ (∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁)) :
    gc71_TwoCommodityLeaf ends K o x y g := by
  refine ⟨D, hDV, hDsrc, hD1, ?_⟩
  intro L hL
  obtain ⟨hrelL, hDsubL⟩ := hrel L hL
  have hconn : connK ends (K ∪ L) o g := gc72_og_in_KL ends hnd K hox hKsrc hL
  exact gc72_ogSurvives_of_relConn ends hnd hog hconn hrelL hDsubL







def gc72_AvoidsO (ends : ι → Sym2 W) (D : Finset ι) (o : W) : Prop :=
    degK ends D o = 0

end Abstract

open Classical













theorem gc72_gc59_connectors :
    ((({1, 2, 3, 4} : Finset (Fin 5)).powerset).filter
      (fun D => sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4))
        ∧ degK gc59_witnessEnds D 3 = 1))
    = ({({1, 2} : Finset (Fin 5)), ({1, 3} : Finset (Fin 5)),
        ({1, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) := by decide






theorem gc72_no_oAvoiding_connector :
    ∀ D : Finset (Fin 5), D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) →
      sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) → degK gc59_witnessEnds D 3 = 1 →
      ¬ gc72_AvoidsO gc59_witnessEnds D 0 := by
  intro D hDV hDsrc hD1
  
  have hVeq : (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) := by
    decide
  rw [hVeq] at hDV
  have hmem : D ∈ ((({1, 2, 3, 4} : Finset (Fin 5)).powerset).filter
      (fun D => sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4))
        ∧ degK gc59_witnessEnds D 3 = 1)) := by
    rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hDV, hDsrc, hD1⟩
  rw [gc72_gc59_connectors] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  
  rw [gc72_AvoidsO]
  rcases hmem with rfl | rfl | rfl <;> decide












theorem gc72_oAvoiding_construction_refuted :
    (∀ D : Finset (Fin 5), D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) →
      sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) → degK gc59_witnessEnds D 3 = 1 →
      ¬ gc72_AvoidsO gc59_witnessEnds D 0)
    ∧ gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨gc72_no_oAvoiding_connector,
    gc72_twoCommodityLeaf_of_removalSurvival gc59_witnessEnds gc59_witnessEnds_loopless _
      (by decide) (by decide) gc59_witnessEnds_K_sources gc71_witness_gc66⟩





theorem gc72_witness_twoCommodityLeaf :
    gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc72_twoCommodityLeaf_of_removalSurvival gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) (by decide) gc59_witnessEnds_K_sources gc71_witness_gc66








theorem gc72_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ x → o ≠ g → sources ends K = ({o, x} : Finset W) →
        (gc71_TwoCommodityLeaf ends K o x y g ↔ gc66_GDeg1RemovalSurvival ends K o x y g))
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W)
      (D : Finset ι),
        o ≠ x → o ≠ g → sources ends K = ({o, x} : Finset W) →
        D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 →
        (∀ L ∈ gc51_LblockSet ends K o x g,
          (∀ P₁ : Finset ι, P₁ ⊆ K ∪ L → sources ends P₁ = ({o, g} : Finset W) →
              connK ends ((K ∪ L) \ P₁) o g)
            ∧ (∃ P₁ : Finset ι, P₁ ⊆ K ∪ L ∧ sources ends P₁ = ({o, g} : Finset W) ∧ D ⊆ P₁)) →
        gc71_TwoCommodityLeaf ends K o x y g)
    ∧ 
    ((∀ D : Finset (Fin 5), D ⊆ (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) →
        sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) → degK gc59_witnessEnds D 3 = 1 →
        ¬ gc72_AvoidsO gc59_witnessEnds D 0)
      ∧ gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3)
    ∧ 
    gc71_TwoCommodityLeaf gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends hnd K o x y g hox hog hKsrc =>
      gc72_twoCommodityLeaf_iff_removalSurvival ends hnd K hox hog hKsrc,
    fun ends hnd K o x y g D hox hog hKsrc hDV hDsrc hD1 hrel =>
      gc72_twoCommodityLeaf_of_relConn ends hnd K hox hog hKsrc hDV hDsrc hD1 hrel,
    gc72_oAvoiding_construction_refuted,
    gc72_witness_twoCommodityLeaf⟩

end StatMech.Walls
