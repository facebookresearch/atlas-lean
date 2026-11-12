/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

















































































































import Mathlib
import Code.Walls.gc68removalsurvival
import Code.Walls.menger_general
import Code.Walls.gc63reroute

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













theorem gc69b_ogReroute_of_disjointConnector (ends : ι → Sym2 W) {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn





theorem gc69b_disjointConnector_of_ogReroute (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {K L D : Finset ι} {o g : W}
    (hog : o ≠ g) (hsurv : connK ends ((K ∪ L) \ D) o g) :
    ∃ P, P ⊆ K ∪ L ∧ Disjoint P D ∧ sources ends P = ({o, g} : Finset W) ∧ connK ends P o g := by
  obtain ⟨P, hPsub, hPsrc⟩ := exists_conn_set ends ((K ∪ L) \ D) hsurv hog
  have hPG : P ⊆ K ∪ L := fun i hi => (Finset.mem_sdiff.1 (hPsub hi)).1
  have hPD : Disjoint P D := by
    rw [Finset.disjoint_left]
    intro i hi
    exact (Finset.mem_sdiff.1 (hPsub hi)).2
  refine ⟨P, hPG, hPD, hPsrc, mng_connK_of_sources ends hnd P hog hPsrc⟩






theorem gc69b_not_isCut_of_disjointConnector (ends : ι → Sym2 W) {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    ¬ mngg_IsCut ends (K ∪ L) o g D := by
  intro hC
  obtain ⟨i, hi⟩ := mngg_cut_meets_connector ends hC hPG hPconn
  rw [Finset.mem_inter] at hi
  exact (Finset.disjoint_left.1 hPD) hi.1 hi.2


















def gc69b_DisjointOGConnector (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∀ D, D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) →
      (∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D') →
      ∀ L ∈ gc51_LblockSet ends K o x g,
        ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W)
          ∧ Disjoint P D ∧ connK ends P o g




theorem gc69b_ogReroute_of_disjointOGConnector (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc69b_DisjointOGConnector ends K o x y g) :
    gc68_OGReroute ends K o x y g := by
  intro D hDV hDsrc hDmin L hL
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ := h D hDV hDsrc hDmin L hL
  exact gc69b_ogReroute_of_disjointConnector ends hPG hPD hPconn




theorem gc69b_disjointOGConnector_of_ogReroute (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hog : o ≠ g)
    (h : gc68_OGReroute ends K o x y g) :
    gc69b_DisjointOGConnector ends K o x y g := by
  intro D hDV hDsrc hDmin L hL
  have hsurv : connK ends ((K ∪ L) \ D) o g := h D hDV hDsrc hDmin L hL
  obtain ⟨P, hPG, hPD, hPsrc, hPconn⟩ := gc69b_disjointConnector_of_ogReroute ends hnd hog hsurv
  exact ⟨P, hPG, hPsrc, hPD, hPconn⟩




theorem gc69b_ogReroute_iff_disjointOGConnector (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hog : o ≠ g) :
    gc68_OGReroute ends K o x y g ↔ gc69b_DisjointOGConnector ends K o x y g :=
  ⟨gc69b_disjointOGConnector_of_ogReroute ends hnd K hog,
    gc69b_ogReroute_of_disjointOGConnector ends K⟩



theorem gc69b_removalSurvival_of_disjointOGConnector (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc69b_DisjointOGConnector ends K o x y g) :
    gc66_GDeg1RemovalSurvival ends K o x y g :=
  gc68_removalSurvival_of_ogReroute ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc
    (gc69b_ogReroute_of_disjointOGConnector ends K h)





theorem gc69b_countIneq_of_disjointOGConnector (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {o x y g : W}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc69b_DisjointOGConnector ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc68_countIneq_of_ogReroute ends hnd hox hoy hog hxy hxg hyg huniv
  intro K hK
  exact gc69b_ogReroute_of_disjointOGConnector ends K (h K hK)















def gc69b_OGSurvival (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
      ∧ (∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D')
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) x g





theorem gc69b_minConnector_gDeg1 (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {y g : W} (hyg : y ≠ g) {D : Finset ι} (hDV : D ⊆ univ \ K)
    (hDsrc : sources ends D = ({y, g} : Finset W))
    (hDmin : ∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D') :
    degK ends D g = 1 := by
  have hodd : Odd (degK ends D g) := gc65_ygConnector_gDeg_odd ends hDsrc
  have hge1 : 1 ≤ degK ends D g := hodd.pos
  by_contra hne
  have hge2 : 2 ≤ degK ends D g := by omega
  obtain ⟨i₀, hi₀D, hi₀g, hi₀conn⟩ := gc67b_removableGEdge ends hnd K hyg D hDV hDsrc hge2
  obtain ⟨D', hD'D, hD'src, hlt⟩ := gc66_strictly_smaller_of_removable ends hyg hi₀D hi₀conn
  have hD'V : D' ⊆ univ \ K := hD'D.trans hDV
  exact absurd (hDmin D' hD'V hD'src) (by omega)





theorem gc69b_removalSurvival_of_ogSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hyg : y ≠ g)
    (h : gc69b_OGSurvival ends K o x y g) :
    gc66_GDeg1RemovalSurvival ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hDmin, hsurv⟩ := h
  exact ⟨D, hDV, hDsrc, gc69b_minConnector_gDeg1 ends hnd K hyg hDV hDsrc hDmin, hsurv⟩





theorem gc69b_countIneq_of_ogSurvival (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc69b_OGSurvival ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc66_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv
  intro K hK
  exact gc69b_removalSurvival_of_ogSurvival ends hnd K hyg (h K hK)














theorem gc69b_relConn2_false_of_bridge (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G C : Finset ι} {o g : W} (hog : o ≠ g)
    (hC : mngg_IsCut ends G o g C) (hC1 : #C = 1) :
    ¬ mngg_RelConn ends G o g 2 := by
  intro hrel
  obtain ⟨⟨P, hP⟩, hcut⟩ := mngg_maxflow_mincut ends hnd hog 2 hrel
  have : (2 : ℕ) ≤ #C := hcut C hC
  omega

end Abstract

open Classical











theorem gc69b_witness_disjointOGConnector :
    gc69b_DisjointOGConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc69b_disjointOGConnector_of_ogReroute gc59_witnessEnds gc59_witnessEnds_loopless
    ({0} : Finset (Fin 5)) (by decide) gc68_witness_ogReroute



theorem gc69b_witness_removalSurvival :
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc69b_removalSurvival_of_disjointOGConnector gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc59_witnessEnds_univ_sources gc59_witnessEnds_K_sources gc69b_witness_disjointOGConnector





theorem gc69b_witness_ogSurvival :
    gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  obtain ⟨D, hDV, hDsrc, hD1, hsurv⟩ := gc66_witness_removalSurvival
  
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
  · 
    intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · exact gc66_witness_surv_23
    · exact gc66_witness_surv_24
    · exact gc66_witness_surv_34


theorem gc69b_witness_removalSurvival_via_ogSurvival :
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc69b_removalSurvival_of_ogSurvival gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) gc69b_witness_ogSurvival









noncomputable def gc69b_bridgeEnds : Fin 1 → Sym2 (Fin 3) := ![s(0, 1)]

theorem gc69b_bridge_loopless : ∀ i : Fin 1, ¬ (gc69b_bridgeEnds i).IsDiag := by decide


theorem gc69b_bridge_isCut :
    mngg_IsCut gc69b_bridgeEnds (univ : Finset (Fin 1)) 0 1 ({0} : Finset (Fin 1)) := by
  refine ⟨by decide, ?_⟩
  intro h
  have hempty : (univ : Finset (Fin 1)) \ ({0} : Finset (Fin 1)) = (∅ : Finset (Fin 1)) := by decide
  rw [hempty] at h
  have inv : ∀ w : Fin 3, connK gc69b_bridgeEnds (∅ : Finset (Fin 1)) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b c _ hstep ih => obtain ⟨i, hi, _⟩ := hstep; simp at hi
  exact absurd (inv 1 h) (by decide)





theorem gc69b_bridge_refutes_menger2 :
    ¬ mngg_RelConn gc69b_bridgeEnds (univ : Finset (Fin 1)) 0 1 2 :=
  gc69b_relConn2_false_of_bridge gc69b_bridgeEnds gc69b_bridge_loopless (by decide)
    gc69b_bridge_isCut (by decide)






















theorem gc69b_refut_D12_min (D' : Finset (Fin 7))
    (hD'V : D' ⊆ (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)))
    (hD'src : sources gc63b_refutEnds D' = ({2, 3} : Finset (Fin 5))) :
    (#({1, 2} : Finset (Fin 7))) ≤ #D' := by
  rcases gc63b_connector_cases hD'V hD'src with rfl | rfl | rfl | rfl <;> decide







theorem gc69b_ogReroute_false :
    ¬ gc68_OGReroute gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3 := by
  intro h
  
  have hDV : ({1, 2} : Finset (Fin 7)) ⊆ (univ : Finset (Fin 7)) \ ({0} : Finset (Fin 7)) := by decide
  have hDsrc : sources gc63b_refutEnds ({1, 2} : Finset (Fin 7)) = ({2, 3} : Finset (Fin 5)) := by decide
  have hLmem : ({1, 2, 5, 6} : Finset (Fin 7))
      ∈ gc51_LblockSet gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 3 := by
    rw [gc63b_refut_LblockSet]; decide
  have hsurv : connK gc63b_refutEnds
      ((({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({1, 2} : Finset (Fin 7))) 0 3 :=
    h ({1, 2} : Finset (Fin 7)) hDV hDsrc gc69b_refut_D12_min
      ({1, 2, 5, 6} : Finset (Fin 7)) hLmem
  rw [show (({0} : Finset (Fin 7)) ∪ ({1, 2, 5, 6} : Finset (Fin 7))) \ ({1, 2} : Finset (Fin 7))
        = ({0, 5, 6} : Finset (Fin 7)) from by decide] at hsurv
  exact gc63b_iso_056_0.2 hsurv







theorem gc69b_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ g →
        (gc68_OGReroute ends K o x y g ↔ gc69b_DisjointOGConnector ends K o x y g))
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W),
        o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
            gc69b_DisjointOGConnector ends K o x y g) →
        gc39_ThreeColouringCountIneq ends o x y g)
    ∧ 
    (¬ mngg_RelConn gc69b_bridgeEnds (univ : Finset (Fin 1)) 0 1 2)
    ∧ 
    (¬ gc68_OGReroute gc63b_refutEnds ({0} : Finset (Fin 7)) 0 1 2 3)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (o x y g : W),
        o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        (∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
            gc69b_OGSurvival ends K o x y g) →
        gc39_ThreeColouringCountIneq ends o x y g)
    ∧ 
    gc69b_DisjointOGConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc69b_OGSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends hnd K o x y g hog => gc69b_ogReroute_iff_disjointOGConnector ends hnd K hog,
    fun ends hnd o x y g hox hoy hog hxy hxg hyg huniv h =>
      gc69b_countIneq_of_disjointOGConnector ends hnd hox hoy hog hxy hxg hyg huniv h,
    gc69b_bridge_refutes_menger2,
    gc69b_ogReroute_false,
    fun ends hnd o x y g hox hoy hog hxy hxg hyg huniv h =>
      gc69b_countIneq_of_ogSurvival ends hnd hox hoy hog hxy hxg hyg huniv h,
    gc69b_witness_disjointOGConnector,
    gc69b_witness_ogSurvival,
    gc69b_witness_removalSurvival⟩

end StatMech.Walls
