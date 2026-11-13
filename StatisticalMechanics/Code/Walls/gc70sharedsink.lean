/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Mathlib
import Code.Walls.gc69mengerclose
import Code.Walls.gc65cyclespace

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











theorem gc70b_ogSurvival_of_disjointConnector (ends : ι → Sym2 W) {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn





theorem gc70b_xgSurvival_of_disjointConnector (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D P : Finset ι} {o x g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K)
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) x g :=
  gc68_xg_survives_of_og ends hnd hox hKsrc hDV
    (gc70b_ogSurvival_of_disjointConnector ends hPG hPD hPconn)















def gc70b_OGConnAvoidingD (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
      ∧ (∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D')
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g,
          ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W)
            ∧ Disjoint P D ∧ connK ends P o g




theorem gc70b_ogSurvival_of_ogConnAvoidingD (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc70b_OGConnAvoidingD ends K o x y g) :
    gc69b_OGSurvival ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hDmin, hL⟩ := h
  refine ⟨D, hDV, hDsrc, hDmin, ?_⟩
  intro L hLmem
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ := hL L hLmem
  exact gc70b_xgSurvival_of_disjointConnector ends hnd hox hKsrc hDV hPG hPD hPconn





theorem gc70b_ogConnAvoidingD_of_ogSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc69b_OGSurvival ends K o x y g) :
    gc70b_OGConnAvoidingD ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hDmin, hsurv⟩ := h
  refine ⟨D, hDV, hDsrc, hDmin, ?_⟩
  intro L hLmem
  have hxg : connK ends ((K ∪ L) \ D) x g := hsurv L hLmem
  have hog' : connK ends ((K ∪ L) \ D) o g :=
    (gc68_xg_iff_og_survives ends hnd hox hKsrc hDV).1 hxg
  obtain ⟨P, hPG, hPD, hPsrc, hPconn⟩ := gc69b_disjointConnector_of_ogReroute ends hnd hog hog'
  exact ⟨P, hPG, hPsrc, hPD, hPconn⟩




theorem gc70b_ogConnAvoidingD_iff_ogSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hog : o ≠ g)
    (hKsrc : sources ends K = ({o, x} : Finset W)) :
    gc70b_OGConnAvoidingD ends K o x y g ↔ gc69b_OGSurvival ends K o x y g :=
  ⟨gc70b_ogSurvival_of_ogConnAvoidingD ends hnd K hox hKsrc,
    gc70b_ogConnAvoidingD_of_ogSurvival ends hnd K hox hog hKsrc⟩





theorem gc70b_countIneq_of_ogConnAvoidingD (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc70b_OGConnAvoidingD ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc69b_countIneq_of_ogSurvival ends hnd hox hoy hog hxy hxg hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc70b_ogSurvival_of_ogConnAvoidingD ends hnd K hox hKsrc (h K hK)
















theorem gc70b_sharedSink_disjoint_of_relConn (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {o g : W} (hog : o ≠ g) (hconn : mngg_RelConn ends G o g 2) :
    ∃ P₀ P₁ : Finset ι, P₀ ⊆ G ∧ P₁ ⊆ G ∧ Disjoint P₀ P₁ ∧
      connK ends P₀ o g ∧ connK ends P₁ o g ∧
      ∀ D : Finset ι, D ⊆ P₀ → connK ends (G \ D) o g := by
  obtain ⟨P, hsub, hsrc, hck, hdisj⟩ := mngg_edgeMenger ends hnd hog 2 hconn
  refine ⟨P 0, P 1, hsub 0, hsub 1, hdisj 0 1 (by decide), hck 0, hck 1, ?_⟩
  intro D hDP0
  
  have hP1D : Disjoint (P 1) D :=
    Finset.disjoint_of_subset_right hDP0 (hdisj 1 0 (by decide))
  exact mng_connK_of_disjoint ends (hsub 1) hP1D (hck 1)




theorem gc70b_sharedSink_survival (ends : ι → Sym2 W) {G D P : Finset ι} {o g : W}
    (hPG : P ⊆ G) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends (G \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn

end Abstract


















open Classical


noncomputable def gc70b_refutEnds : Fin 4 → Sym2 (Fin 4) := ![s(0, 1), s(1, 3), s(1, 3), s(2, 3)]

theorem gc70b_refutEnds_loopless : ∀ i : Fin 4, ¬ (gc70b_refutEnds i).IsDiag := by decide




theorem gc70b_refut_isCut :
    mngg_IsCut gc70b_refutEnds ({0, 1} : Finset (Fin 4)) 0 3 ({1} : Finset (Fin 4)) := by
  refine ⟨by decide, ?_⟩
  intro h
  have hset : (({0, 1} : Finset (Fin 4)) \ ({1} : Finset (Fin 4))) = ({0} : Finset (Fin 4)) := by decide
  rw [hset] at h
  
  have inv : ∀ w : Fin 4, connK gc70b_refutEnds ({0} : Finset (Fin 4)) 0 w → w = 0 ∨ w = 1 := by
    intro w hw
    induction hw with
    | refl => exact Or.inl rfl
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hb, hc, hbc⟩ := hstep
      simp only [Finset.mem_singleton] at hi
      subst hi
      
      fin_cases c <;> simp_all [gc70b_refutEnds]
  rcases inv 3 h with h0 | h1 <;> simp_all






theorem gc70b_superSource_route_refuted :
    ¬ mngg_RelConn gc70b_refutEnds ({0, 1} : Finset (Fin 4)) 0 3 2 :=
  gc69b_relConn2_false_of_bridge gc70b_refutEnds gc70b_refutEnds_loopless (by decide)
    gc70b_refut_isCut (by decide)









theorem gc70b_witness_P3_src :
    sources gc59_witnessEnds ({3} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) := by decide


theorem gc70b_witness_P4_src :
    sources gc59_witnessEnds ({4} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) := by decide


theorem gc70b_witness_P3_conn : connK gc59_witnessEnds ({3} : Finset (Fin 5)) 0 3 :=
  Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc70b_witness_P4_conn : connK gc59_witnessEnds ({4} : Finset (Fin 5)) 0 3 :=
  Relation.ReflTransGen.single ⟨4, by decide, by decide, by decide, by decide⟩








theorem gc70b_witness_ogConnAvoidingD :
    gc70b_OGConnAvoidingD gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine ⟨({1, 2} : Finset (Fin 5)), ?_, gc59_witnessEnds_D_sources, ?_, ?_⟩
  · rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
    decide
  · 
    intro D' hD'V hD'src
    have hVeq : (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) := by decide
    rw [hVeq] at hD'V
    have hlb : ∀ D'' ∈ ({1, 2, 3, 4} : Finset (Fin 5)).powerset,
        sources gc59_witnessEnds D'' = ({2, 3} : Finset (Fin 4)) → 2 ≤ #D'' := by decide
    have := hlb D' (Finset.mem_powerset.2 hD'V) hD'src
    simpa using this
  · intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · 
      refine ⟨({3} : Finset (Fin 5)), ?_, gc70b_witness_P3_src, by decide, gc70b_witness_P3_conn⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) = ({0, 2, 3} : Finset (Fin 5)) from by decide]
      decide
    · 
      refine ⟨({4} : Finset (Fin 5)), ?_, gc70b_witness_P4_src, by decide, gc70b_witness_P4_conn⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) = ({0, 2, 4} : Finset (Fin 5)) from by decide]
      decide
    · 
      refine ⟨({3} : Finset (Fin 5)), ?_, gc70b_witness_P3_src, by decide, gc70b_witness_P3_conn⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) = ({0, 3, 4} : Finset (Fin 5)) from by decide]
      decide


theorem gc70b_witness_ogSurvival :
    gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc70b_ogSurvival_of_ogConnAvoidingD gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) gc59_witnessEnds_K_sources gc70b_witness_ogConnAvoidingD


theorem gc70b_witness_removalSurvival :
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc69b_removalSurvival_of_ogSurvival gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) gc70b_witness_ogSurvival








theorem gc70b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ x → o ≠ g → sources ends K = ({o, x} : Finset W) →
        (gc70b_OGConnAvoidingD ends K o x y g ↔ gc69b_OGSurvival ends K o x y g))
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W),
        o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
            gc70b_OGConnAvoidingD ends K o x y g) →
        gc39_ThreeColouringCountIneq ends o x y g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (G : Finset ι) (o g : W),
        o ≠ g → mngg_RelConn ends G o g 2 →
        ∃ P₀ P₁ : Finset ι, P₀ ⊆ G ∧ P₁ ⊆ G ∧ Disjoint P₀ P₁ ∧
          connK ends P₀ o g ∧ connK ends P₁ o g ∧
          ∀ D : Finset ι, D ⊆ P₀ → connK ends (G \ D) o g)
    ∧ 
    (¬ mngg_RelConn gc70b_refutEnds ({0, 1} : Finset (Fin 4)) 0 3 2)
    ∧ 
    gc70b_OGConnAvoidingD gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends hnd K o x y g hox hog hKsrc => gc70b_ogConnAvoidingD_iff_ogSurvival ends hnd K hox hog hKsrc,
    fun ends hnd o x y g hox hoy hog hxy hxg hyg huniv h =>
      gc70b_countIneq_of_ogConnAvoidingD ends hnd hox hoy hog hxy hxg hyg huniv h,
    fun ends hnd G o g hog hconn => gc70b_sharedSink_disjoint_of_relConn ends hnd hog hconn,
    gc70b_superSource_route_refuted,
    gc70b_witness_ogConnAvoidingD,
    gc70b_witness_ogSurvival,
    gc70b_witness_removalSurvival⟩

end StatMech.Walls
