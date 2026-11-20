/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Walls.gc52switchinj

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





theorem gc53_ox_conn_of_sources (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x : W} (hox : o ≠ x) (hKsrc : sources ends K = ({o, x} : Finset W)) :
    connK ends K o x := by
  apply path_exists ends K (fun i _ => hnd i) o x
  · rw [← mem_sources, hKsrc]; simp
  · intro z hz; rw [← mem_sources, hKsrc] at hz; simpa using hz
  · exact hox










theorem gc53_allConn_iff_xg_gate (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K Q : Finset ι) {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hQsrc : sources ends Q = ({y, g} : Finset W)) :
    (connK ends (K ∪ Q) o x ∧ connK ends (K ∪ Q) o y ∧ connK ends (K ∪ Q) o g)
      ↔ connK ends (K ∪ Q) x g := by
  have hox_conn : connK ends (K ∪ Q) o x :=
    gc51_connK_mono ends Finset.subset_union_left
      (gc53_ox_conn_of_sources ends hnd K hox hKsrc)
  have hyg_conn : connK ends (K ∪ Q) y g :=
    gc51_connK_mono ends Finset.subset_union_right
      (gc51_connK_of_sources ends hnd Q hyg hQsrc)
  constructor
  · rintro ⟨_, _, hog⟩
    
    exact (connK_symm ends _ hox_conn).trans hog
  · intro hxg
    
    have hog : connK ends (K ∪ Q) o g := hox_conn.trans hxg
    have hoy : connK ends (K ∪ Q) o y := hog.trans (connK_symm ends _ hyg_conn)
    exact ⟨hox_conn, hoy, hog⟩







theorem gc53_Rblock_eq_gateBlock (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    gc51_RblockSet ends K o x y g
      = (univ \ K).powerset.filter
          (fun Q => sources ends Q = ({y, g} : Finset W) ∧ connK ends (K ∪ Q) x g) := by
  rw [gc51_RblockSet]
  apply Finset.filter_congr
  intro Q hQ
  by_cases hQsrc : sources ends Q = ({y, g} : Finset W)
  · 
    have hiff := gc53_allConn_iff_xg_gate ends hnd K Q hox hyg hKsrc hQsrc
    constructor
    · rintro ⟨_, hax, hay, hag⟩; exact ⟨hQsrc, hiff.1 ⟨hax, hay, hag⟩⟩
    · rintro ⟨_, hxg⟩; obtain ⟨hax, hay, hag⟩ := hiff.2 hxg; exact ⟨hQsrc, hax, hay, hag⟩
  · 
    constructor
    · rintro ⟨h, _⟩; exact absurd h hQsrc
    · rintro ⟨h, _⟩; exact absurd h hQsrc






theorem gc53_exists_fixedPath (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι)
    {o x y g : W} (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    ∃ P₀, P₀ ⊆ univ \ K ∧ sources ends P₀ = ({y, g} : Finset W) := by
  have hVsrc : sources ends (univ \ K) = ({y, g} : Finset W) :=
    gc51_complSources ends K hoy hog hxy hxg huniv hKsrc
  have hyg_conn : connK ends (univ \ K) y g := by
    apply path_exists ends (univ \ K) (fun i _ => hnd i) y g
    · rw [← mem_sources, hVsrc]; simp
    · intro z hz; rw [← mem_sources, hVsrc] at hz; simpa using hz
    · exact hyg
  obtain ⟨P₀, hP₀sub, hP₀src⟩ := exists_conn_set ends (univ \ K) hyg_conn hyg
  exact ⟨P₀, hP₀sub, hP₀src⟩



noncomputable def gc53_cosetGateBlock (ends : ι → Sym2 W) (K P₀ : Finset ι) (o x g : W) :
    Finset (Finset ι) :=
  (univ \ K).powerset.filter
    (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ (L ∆ P₀)) x g)










theorem gc53_Rblock_card_eq_cosetGate (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hyg : y ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    {P₀ : Finset ι} (hP₀sub : P₀ ⊆ univ \ K) (hP₀src : sources ends P₀ = ({y, g} : Finset W)) :
    #(gc51_RblockSet ends K o x y g) = #(gc53_cosetGateBlock ends K P₀ o x g) := by
  rw [gc53_Rblock_eq_gateBlock ends hnd K hox hyg hKsrc, gc53_cosetGateBlock]
  
  rw [show ((univ \ K).powerset.filter
        (fun Q => sources ends Q = ({y, g} : Finset W) ∧ connK ends (K ∪ Q) x g))
      = ((univ \ K).powerset.filter
          (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ (L ∆ P₀)) x g)).image
            (fun L => L ∆ P₀) from ?_]
  · rw [Finset.card_image_of_injOn]
    intro a ha b hb hab
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_powerset] at ha hb
    simp only at hab
    have : (a ∆ P₀) ∆ P₀ = (b ∆ P₀) ∆ P₀ := by rw [hab]
    rwa [symmDiff_symmDiff_cancel_right, symmDiff_symmDiff_cancel_right] at this
  · ext Q
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_image]
    constructor
    · rintro ⟨hQV, hQsrc, hgate⟩
      
      refine ⟨Q ∆ P₀, ⟨?_, ?_, ?_⟩, ?_⟩
      · 
        intro i hi
        rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨h, _⟩ | ⟨h, _⟩
        · exact hQV h
        · exact hP₀sub h
      · 
        rw [sources_symmDiff, hQsrc, hP₀src, symmDiff_self]; rfl
      · 
        rwa [symmDiff_symmDiff_cancel_right]
      · 
        rw [symmDiff_symmDiff_cancel_right]
    · rintro ⟨L, ⟨hLV, hLsrc, hgate⟩, rfl⟩
      refine ⟨?_, ?_, hgate⟩
      · 
        intro i hi
        rw [Finset.mem_symmDiff] at hi
        rcases hi with ⟨h, _⟩ | ⟨h, _⟩
        · exact hLV h
        · exact hP₀sub h
      · 
        rw [sources_symmDiff, hLsrc, hP₀src]; simp


















def gc53_CosetGateDom (ends : ι → Sym2 W) (o x y g : W) : Prop :=
    ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      ∀ P₀ ⊆ univ \ K, sources ends P₀ = ({y, g} : Finset W) →
        #(gc51_LblockSet ends K o x g) ≤ #(gc53_cosetGateBlock ends K P₀ o x g)



theorem gc53_LblockSet_eq_gateBlock (ends : ι → Sym2 W) (K : Finset ι) (o x g : W) :
    gc51_LblockSet ends K o x g
      = (univ \ K).powerset.filter
          (fun L => sources ends L = (∅ : Finset W) ∧ connK ends (K ∪ L) x g) := rfl





theorem gc53_Lblock_le_Rblock_of_cosetGateDom (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hdom : gc53_CosetGateDom ends o x y g)
    (K : Finset ι) (hK : K ∈ (univ : Finset ι).powerset.filter
      (fun K => sources ends K = ({o, x} : Finset W))) :
    #(gc51_LblockSet ends K o x g) ≤ #(gc51_RblockSet ends K o x y g) := by
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  obtain ⟨P₀, hP₀sub, hP₀src⟩ :=
    gc53_exists_fixedPath ends hnd K hoy hog hxy hxg hyg huniv hKsrc
  have h1 : #(gc51_LblockSet ends K o x g) ≤ #(gc53_cosetGateBlock ends K P₀ o x g) :=
    hdom K hK P₀ hP₀sub hP₀src
  have h2 : #(gc51_RblockSet ends K o x y g) = #(gc53_cosetGateBlock ends K P₀ o x g) :=
    gc53_Rblock_card_eq_cosetGate ends hnd K hox hyg hKsrc hP₀sub hP₀src
  rw [h2]; exact h1




theorem gc53_perKCount_of_cosetGateDom (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hdom : gc53_CosetGateDom ends o x y g) :
    gc52_PerKCount ends o x y g := by
  intro K hK
  rw [← gc51_LblockSet_card, ← gc51_RblockSet_card]
  exact gc53_Lblock_le_Rblock_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv hdom K hK




theorem gc53_countIneq_of_cosetGateDom (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hdom : gc53_CosetGateDom ends o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g :=
  gc52_countIneq_of_perKCount ends hnd hox hoy hog hxy hxg hyg huniv
    (gc53_perKCount_of_cosetGateDom ends hnd hox hoy hog hxy hxg hyg huniv hdom)

end Abstract

open Classical














theorem gc53_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  intro K hK P₀ hP₀sub hP₀src
  
  have hKsrc : sources gc49_witnessEnds K = ({0, 1} : Finset (Fin 4)) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  have hbij : #(gc51_RblockSet gc49_witnessEnds K 0 1 2 3)
      = #(gc53_cosetGateBlock gc49_witnessEnds K P₀ 0 1 3) :=
    gc53_Rblock_card_eq_cosetGate gc49_witnessEnds gc49_witnessEnds_loopless K
      (by decide) (by decide) hKsrc hP₀sub hP₀src
  rw [← hbij]
  
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · rw [gc51_witness_LblockSet_K13, gc51_witness_RblockSet_K13, Finset.card_singleton,
      Finset.card_singleton]
  · rw [gc51_witness_LblockSet_K23, gc51_witness_RblockSet_K23, Finset.card_singleton,
      Finset.card_singleton]




theorem gc53_witness_perKCount : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc53_perKCount_of_cosetGateDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc49_witnessEnds_univ_sources gc53_witness_cosetGateDom






theorem gc53_witness_Rblock_gate_K13 :
    gc51_RblockSet gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3
      = (univ \ ({1, 3} : Finset (Fin 4))).powerset.filter
          (fun Q => sources gc49_witnessEnds Q = ({2, 3} : Finset (Fin 4))
            ∧ connK gc49_witnessEnds (({1, 3} : Finset (Fin 4)) ∪ Q) 1 3) :=
  gc53_Rblock_eq_gateBlock gc49_witnessEnds gc49_witnessEnds_loopless
    ({1, 3} : Finset (Fin 4)) (by decide) (by decide) (by decide)

end StatMech.Walls
