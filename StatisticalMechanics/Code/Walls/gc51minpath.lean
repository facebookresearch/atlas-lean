/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































































import Mathlib
import Code.Walls.gc50threereplica

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

open StatMech.Sharpness.RandomCurrent (sources connK degK adjStep compOf switching_card
  switching_card₂ connK_symm exists_conn_set sources_symmDiff path_exists mem_sources)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]





theorem gc51_connK_mono (ends : ι → Sym2 W) {K₁ K₂ : Finset ι} (h : K₁ ⊆ K₂) {a b : W}
    (hab : connK ends K₁ a b) : connK ends K₂ a b := by
  refine Relation.ReflTransGen.mono ?_ hab
  rintro p q ⟨i, hi, hp, hq, hpq⟩
  exact ⟨i, h hi, hp, hq, hpq⟩


theorem gc51_connK_of_sources (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (P : Finset ι) {y g : W} (hyg : y ≠ g) (hPsrc : sources ends P = ({y, g} : Finset W)) :
    connK ends P y g := by
  apply path_exists ends P (fun i _ => hnd i) y g
  · rw [← mem_sources, hPsrc]; simp
  · intro z hz; rw [← mem_sources, hPsrc] at hz; simpa using hz
  · exact hyg



theorem gc51_sdiff_sources (ends : ι → Sym2 W) {V L : Finset ι} (hLV : L ⊆ V) {y g : W}
    (hVsrc : sources ends V = ({y, g} : Finset W)) (hLsrc : sources ends L = (∅ : Finset W)) :
    sources ends (V \ L) = ({y, g} : Finset W) := by
  have hcompl : V \ L = V ∆ L := (symmDiff_of_ge hLV).symm
  rw [hcompl, sources_symmDiff, hVsrc, hLsrc]
  simp





theorem gc51_exists_remPath (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {V L : Finset ι}
    (hLV : L ⊆ V) {y g : W} (hyg : y ≠ g)
    (hVsrc : sources ends V = ({y, g} : Finset W)) (hLsrc : sources ends L = (∅ : Finset W)) :
    ∃ P, P ⊆ V \ L ∧ sources ends P = ({y, g} : Finset W) := by
  have hVLsrc : sources ends (V \ L) = ({y, g} : Finset W) :=
    gc51_sdiff_sources ends hLV hVsrc hLsrc
  
  have hyg_conn : connK ends (V \ L) y g := by
    apply path_exists ends (V \ L) (fun i _ => hnd i) y g
    · rw [← mem_sources, hVLsrc]; simp
    · intro z hz
      rw [← mem_sources, hVLsrc] at hz
      simpa using hz
    · exact hyg
  obtain ⟨P, hPsub, hPsrc⟩ := exists_conn_set ends (V \ L) hyg_conn hyg
  exact ⟨P, hPsub, hPsrc⟩


theorem gc51_remPath_disjoint {ι : Type*} [DecidableEq ι] {V L P : Finset ι}
    (hP : P ⊆ V \ L) : Disjoint L P := by
  rw [Finset.disjoint_left]
  intro i hiL hiP
  have := hP hiP
  rw [Finset.mem_sdiff] at this
  exact this.2 hiL








theorem gc51_mapsInto (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι)
    {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {V L P : Finset ι} (hLV : L ⊆ V) (hPVL : P ⊆ V \ L)
    (hLsrc : sources ends L = (∅ : Finset W)) (hPsrc : sources ends P = ({y, g} : Finset W))
    (hgate : connK ends (K ∪ L) x g) :
    (L ∪ P) ⊆ V ∧ sources ends (L ∪ P) = ({y, g} : Finset W)
      ∧ connK ends (K ∪ (L ∪ P)) o x ∧ connK ends (K ∪ (L ∪ P)) o y
        ∧ connK ends (K ∪ (L ∪ P)) o g := by
  have hdisj : Disjoint L P := gc51_remPath_disjoint hPVL
  have hPV : P ⊆ V := fun i hi => (Finset.mem_sdiff.1 (hPVL hi)).1
  
  have hQV : (L ∪ P) ⊆ V := Finset.union_subset hLV hPV
  
  have hQsrc : sources ends (L ∪ P) = ({y, g} : Finset W) := by
    have hun : L ∪ P = L ∆ P := (Disjoint.symmDiff_eq_sup hdisj).symm
    rw [hun, sources_symmDiff, hLsrc, hPsrc]
    simp
  
  have hox_conn : connK ends (K ∪ (L ∪ P)) o x := by
    have hox_K : connK ends K o x := by
      apply path_exists ends K (fun i _ => hnd i) o x
      · rw [← mem_sources, hKsrc]; simp
      · intro z hz; rw [← mem_sources, hKsrc] at hz; simpa using hz
      · exact hox
    exact gc51_connK_mono ends (Finset.subset_union_left) hox_K
  have hxg_conn : connK ends (K ∪ (L ∪ P)) x g :=
    gc51_connK_mono ends (Finset.union_subset_union_right (Finset.subset_union_left)) hgate
  have hyg_conn : connK ends (K ∪ (L ∪ P)) y g := by
    have hyg_P : connK ends P y g := gc51_connK_of_sources ends hnd P hyg hPsrc
    have hPsub : P ⊆ K ∪ (L ∪ P) := by
      intro i hi; exact Finset.mem_union_right _ (Finset.mem_union_right _ hi)
    exact gc51_connK_mono ends hPsub hyg_P
  
  have hog_conn : connK ends (K ∪ (L ∪ P)) o g := hox_conn.trans hxg_conn
  have hoy_conn : connK ends (K ∪ (L ∪ P)) o y :=
    hog_conn.trans (connK_symm ends _ hyg_conn)
  exact ⟨hQV, hQsrc, hox_conn, hoy_conn, hog_conn⟩










noncomputable def gc51_LblockSet (ends : ι → Sym2 W) (K : Finset ι) (o x g : W) : Finset (Finset ι) :=
  (univ \ K).powerset.filter (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ L) x g)



noncomputable def gc51_RblockSet (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) :
    Finset (Finset ι) :=
  (univ \ K).powerset.filter (fun Q => sources ends Q = ({y, g} : Finset W)
      ∧ connK ends (K ∪ Q) o x ∧ connK ends (K ∪ Q) o y ∧ connK ends (K ∪ Q) o g)


theorem gc51_LblockSet_card (ends : ι → Sym2 W) (K : Finset ι) (o x g : W) :
    #(gc51_LblockSet ends K o x g) = gc50_Lblock ends K o x g := rfl


theorem gc51_RblockSet_card (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) :
    #(gc51_RblockSet ends K o x y g) = gc50_Rblock ends K o x y g := rfl





















def gc51_SwitchInjective (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ P : Finset ι → Finset ι,
      (∀ L ∈ gc51_LblockSet ends K o x g,
          P L ⊆ univ \ K ∧ sources ends (P L) = ({y, g} : Finset W)
            ∧ (L ∆ P L) ∈ gc51_RblockSet ends K o x y g)
        ∧ Set.InjOn (fun L => L ∆ P L) (gc51_LblockSet ends K o x g : Set (Finset ι))




theorem gc51_perK_dom_of_switchInjective (ends : ι → Sym2 W)
    (K : Finset ι) {o x y g : W}
    (h : gc51_SwitchInjective ends K o x y g) :
    gc50_Lblock ends K o x g ≤ gc50_Rblock ends K o x y g := by
  obtain ⟨P, hP, hinj⟩ := h
  rw [← gc51_LblockSet_card, ← gc51_RblockSet_card]
  apply Finset.card_le_card_of_injOn (fun L => L ∆ P L)
  · 
    intro L hL
    rw [Finset.mem_coe] at hL
    obtain ⟨_, _, hQ⟩ := hP L hL
    rw [Finset.mem_coe]
    exact hQ
  · 
    exact hinj







theorem gc51_disjoint_mapsInto (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {L P : Finset ι} (hL : L ∈ gc51_LblockSet ends K o x g)
    (hPVL : P ⊆ (univ \ K) \ L) (hPsrc : sources ends P = ({y, g} : Finset W)) :
    (L ∆ P) ∈ gc51_RblockSet ends K o x y g := by
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨hLV, hLsrc, hgate⟩ := hL
  obtain ⟨hQV, hQsrc, hoxQ, hoyQ, hogQ⟩ :=
    gc51_mapsInto ends hnd K hox hyg hKsrc hLV hPVL hLsrc hPsrc hgate
  have hdisj : Disjoint L P := gc51_remPath_disjoint hPVL
  have hun : L ∆ P = L ∪ P := Disjoint.symmDiff_eq_sup hdisj
  rw [gc51_RblockSet, Finset.mem_filter, Finset.mem_powerset, hun]
  exact ⟨hQV, hQsrc, hoxQ, hoyQ, hogQ⟩






theorem gc51_complSources (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    sources ends (univ \ K) = ({y, g} : Finset W) := by
  rw [gc40_sources_compl, huniv, hKsrc]
  exact gc50_sd_oxyg_ox hoy hog hxy hxg




theorem gc51_perKDom_of_switchInjective (ends : ι → Sym2 W)
    {o x y g : W}
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc51_SwitchInjective ends K o x y g) :
    gc50_PerKDom ends o x y g := by
  intro K hK
  exact gc51_perK_dom_of_switchInjective ends K (h K hK)




theorem gc51_countIneq_of_switchInjective (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc51_SwitchInjective ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc50_countIneq_of_perKDom ends hnd hox hoy hog hxy hxg hyg huniv
    (gc51_perKDom_of_switchInjective ends h)

end Abstract

open Classical













theorem gc51_witness_LblockSet_K13 :
    gc51_LblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 3 = {(∅ : Finset (Fin 4))} := by
  rw [gc51_LblockSet]
  have hV : (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 2} : Finset (Fin 4)).powerset.filter
      (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))
      = {(∅ : Finset (Fin 4))} := by decide
  rw [show ({0, 2} : Finset (Fin 4)).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3)
      = (({0, 2} : Finset (Fin 4)).powerset.filter
          (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hconn : connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) 1 3 := by
    rw [Finset.union_empty]
    exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos hconn]


theorem gc51_witness_LblockSet_K23 :
    gc51_LblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 3 = {(∅ : Finset (Fin 4))} := by
  rw [gc51_LblockSet]
  have hV : (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 1} : Finset (Fin 4)).powerset.filter
      (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))
      = {(∅ : Finset (Fin 4))} := by decide
  rw [show ({0, 1} : Finset (Fin 4)).powerset.filter
        (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ L) 1 3)
      = (({0, 1} : Finset (Fin 4)).powerset.filter
          (fun L => sources gc49_witnessEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hconn : connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ (∅ : Finset (Fin 4))) 1 3 := by
    rw [Finset.union_empty]
    exact Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos hconn]


theorem gc51_witness_RblockSet_K13 :
    gc51_RblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3
      = {({0, 2} : Finset (Fin 4))} := by
  rw [gc51_RblockSet]
  have hV : (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 2} : Finset (Fin 4)).powerset.filter
      (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))
      = {({0, 2} : Finset (Fin 4))} := by decide
  rw [show ({0, 2} : Finset (Fin 4)).powerset.filter
        (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 1
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 2
          ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 3)
      = (({0, 2} : Finset (Fin 4)).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))).filter
            (fun Q => connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 1
              ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 2
              ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 0 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hunivEq : ({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4)) = (univ : Finset (Fin 4)) := by
    decide
  have hconn : connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 1
      ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 2
      ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ ({0, 2} : Finset (Fin 4))) 0 3 := by
    rw [hunivEq]; exact gc50_witness_univ_allConn
  rw [Finset.filter_singleton, if_pos hconn]


theorem gc51_witness_RblockSet_K23 :
    gc51_RblockSet gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3
      = {({0, 1} : Finset (Fin 4))} := by
  rw [gc51_RblockSet]
  have hV : (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) := by
    decide
  rw [hV]
  have hset : ({0, 1} : Finset (Fin 4)).powerset.filter
      (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))
      = {({0, 1} : Finset (Fin 4))} := by decide
  rw [show ({0, 1} : Finset (Fin 4)).powerset.filter
        (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 1
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 2
          ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 3)
      = (({0, 1} : Finset (Fin 4)).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4)))).filter
            (fun Q => connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 1
              ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 2
              ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ Q) 0 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hunivEq : ({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4)) = (univ : Finset (Fin 4)) := by
    decide
  have hconn : connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 1
      ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 2
      ∧ connK gc49_witnessEnds (({2, 3} : Finset (Fin 4)) ∪ ({0, 1} : Finset (Fin 4))) 0 3 := by
    rw [hunivEq]; exact gc50_witness_univ_allConn
  rw [Finset.filter_singleton, if_pos hconn]




theorem gc51_witness_switchInjective_K13 :
    gc51_SwitchInjective gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
  refine ⟨fun _ => (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)), ?_, ?_⟩
  · intro L hL
    rw [gc51_witness_LblockSet_K13, Finset.mem_singleton] at hL
    subst hL
    refine ⟨Finset.Subset.refl _, ?_, ?_⟩
    · decide
    · rw [gc51_witness_RblockSet_K13, Finset.mem_singleton]; decide
  · rw [gc51_witness_LblockSet_K13]
    intro a ha b hb _
    rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
    rw [ha, hb]


theorem gc51_witness_switchInjective_K23 :
    gc51_SwitchInjective gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
  refine ⟨fun _ => (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)), ?_, ?_⟩
  · intro L hL
    rw [gc51_witness_LblockSet_K23, Finset.mem_singleton] at hL
    subst hL
    refine ⟨Finset.Subset.refl _, ?_, ?_⟩
    · decide
    · rw [gc51_witness_RblockSet_K23, Finset.mem_singleton]; decide
  · rw [gc51_witness_LblockSet_K23]
    intro a ha b hb _
    rw [Finset.mem_coe, Finset.mem_singleton] at ha hb
    rw [ha, hb]






theorem gc51_witness_perKDom_via_switchInjective :
    gc50_PerKDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc51_perKDom_of_switchInjective gc49_witnessEnds
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc51_witness_switchInjective_K13
  · exact gc51_witness_switchInjective_K23





theorem gc51_witness_EMassResidue_via_switchInjective :
    gc42_EMassResidue gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc50_EMassResidue_of_perKDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide)
    gc51_witness_perKDom_via_switchInjective












noncomputable def gc51_ceEnds : Fin 2 → Sym2 (Fin 4) := ![s(0, 3), s(1, 3)]


theorem gc51_ceEnds_univ_sources :
    sources gc51_ceEnds (univ : Finset (Fin 2)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc51_ce_Rblock_zero :
    gc50_Rblock gc51_ceEnds ({0, 1} : Finset (Fin 2)) 0 1 2 3 = 0 := by
  rw [gc50_Rblock]
  have hV : (univ : Finset (Fin 2)) \ ({0, 1} : Finset (Fin 2)) = (∅ : Finset (Fin 2)) := by decide
  rw [hV]; decide


theorem gc51_ce_Lblock_one :
    gc50_Lblock gc51_ceEnds ({0, 1} : Finset (Fin 2)) 0 1 3 = 1 := by
  rw [gc50_Lblock]
  have hV : (univ : Finset (Fin 2)) \ ({0, 1} : Finset (Fin 2)) = (∅ : Finset (Fin 2)) := by decide
  rw [hV]
  have hset : (∅ : Finset (Fin 2)).powerset.filter
      (fun L => sources gc51_ceEnds L = (∅ : Finset (Fin 4))) = {(∅ : Finset (Fin 2))} := by decide
  rw [show (∅ : Finset (Fin 2)).powerset.filter
        (fun L => sources gc51_ceEnds L = (∅ : Finset (Fin 4))
          ∧ connK gc51_ceEnds (({0, 1} : Finset (Fin 2)) ∪ L) 1 3)
      = ((∅ : Finset (Fin 2)).powerset.filter
          (fun L => sources gc51_ceEnds L = (∅ : Finset (Fin 4)))).filter
            (fun L => connK gc51_ceEnds (({0, 1} : Finset (Fin 2)) ∪ L) 1 3) from by
    rw [Finset.filter_filter]]
  rw [hset]
  have hconn : connK gc51_ceEnds (({0, 1} : Finset (Fin 2)) ∪ (∅ : Finset (Fin 2))) 1 3 := by
    rw [Finset.union_empty]
    exact Relation.ReflTransGen.single ⟨1, by decide, by decide, by decide, by decide⟩
  rw [Finset.filter_singleton, if_pos hconn, Finset.card_singleton]





theorem gc51_perKDom_false_without_huniv :
    ¬ gc50_PerKDom gc51_ceEnds (0 : Fin 4) 1 2 3 := by
  intro h
  have hK : ({0, 1} : Finset (Fin 2)) ∈ (univ : Finset (Fin 2)).powerset.filter
      (fun K => sources gc51_ceEnds K = ({0, 1} : Finset (Fin 4))) := by decide
  have hle := h ({0, 1} : Finset (Fin 2)) hK
  rw [gc51_ce_Lblock_one, gc51_ce_Rblock_zero] at hle
  exact absurd hle (by norm_num)

end StatMech.Walls
