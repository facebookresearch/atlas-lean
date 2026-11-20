/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/








































































import Mathlib
import Code.Walls.gc67removable
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





theorem gc68_K_survives {K L D : Finset ι} (hDV : D ⊆ univ \ K) :
    K ⊆ (K ∪ L) \ D := by
  intro i hiK
  rw [Finset.mem_sdiff]
  refine ⟨Finset.mem_union_left _ hiK, ?_⟩
  intro hiD
  exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK




theorem gc68_ox_survives (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o x : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K) :
    connK ends ((K ∪ L) \ D) o x := by
  have hoxK : connK ends K o x := by
    apply path_exists ends K (fun i _ => hnd i) o x
    · rw [← mem_sources, hKsrc]; simp
    · intro z hz; rw [← mem_sources, hKsrc] at hz; simpa using hz
    · exact hox
  exact mng_connK_mono ends (gc68_K_survives hDV) hoxK



theorem gc68_xg_iff_og_survives (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o x g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K) :
    connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g := by
  have hox' : connK ends ((K ∪ L) \ D) o x := gc68_ox_survives ends hnd hox hKsrc hDV
  constructor
  · intro hxg; exact hox'.trans hxg
  · intro hog; exact (connK_symm ends _ hox').trans hog




theorem gc68_xg_survives_of_og (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {K L D : Finset ι} {o x g : W} (hox : o ≠ x)
    (hKsrc : sources ends K = ({o, x} : Finset W)) (hDV : D ⊆ univ \ K)
    (hog : connK ends ((K ∪ L) \ D) o g) :
    connK ends ((K ∪ L) \ D) x g :=
  (gc68_xg_iff_og_survives ends hnd hox hKsrc hDV).2 hog







theorem gc68b_xg_avoids_D_of_disjointConnector (ends : ι → Sym2 W) {K L D P : Finset ι} {x g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P x g) :
    connK ends ((K ∪ L) \ D) x g :=
  mng_connK_of_disjoint ends hPG hPD hPconn



theorem gc68b_xg_avoids_D_of_boundaryConnector (ends : ι → Sym2 W) {K L D P : Finset ι} {x g : W}
    (hPG : P ⊆ K ∪ L) (hPsrc : sources ends P = ({x, g} : Finset W)) (hPD : Disjoint P D)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (hxg : x ≠ g) :
    connK ends ((K ∪ L) \ D) x g := by
  have hPconn : connK ends P x g := by
    apply path_exists ends P (fun i _ => hnd i) x g
    · rw [← mem_sources, hPsrc]; simp
    · intro z hz; rw [← mem_sources, hPsrc] at hz; simpa using hz
    · exact hxg
  exact gc68b_xg_avoids_D_of_disjointConnector ends hPG hPD hPconn












def gc68_OGReroute (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∀ D, D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) →
      (∀ D', D' ⊆ univ \ K → sources ends D' = ({y, g} : Finset W) → #D ≤ #D') →
      ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g










theorem gc68_removalSurvival_of_ogReroute (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g)
    (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc68_OGReroute ends K o x y g) :
    gc66_GDeg1RemovalSurvival ends K o x y g := by
  
  obtain ⟨D, hDV, hDsrc, hDmin⟩ :=
    gc63b_minConnector ends hnd K hoy hog hxy hxg hyg huniv hKsrc
  
  have hD1 : degK ends D g = 1 := by
    have hodd : Odd (degK ends D g) := gc65_ygConnector_gDeg_odd ends hDsrc
    have hge1 : 1 ≤ degK ends D g := hodd.pos
    by_contra hne
    have hge2 : 2 ≤ degK ends D g := by omega
    obtain ⟨i₀, hi₀D, hi₀g, hi₀conn⟩ :=
      gc67b_removableGEdge ends hnd K hyg D hDV hDsrc hge2
    obtain ⟨D', hD'D, hD'src, hlt⟩ := gc66_strictly_smaller_of_removable ends hyg hi₀D hi₀conn
    have hD'V : D' ⊆ univ \ K := hD'D.trans hDV
    exact absurd (hDmin D' hD'V hD'src) (by omega)
  refine ⟨D, hDV, hDsrc, hD1, ?_⟩
  intro L hL
  have hog' : connK ends ((K ∪ L) \ D) o g := h D hDV hDsrc hDmin L hL
  exact gc68_xg_survives_of_og ends hnd hox hKsrc hDV hog'



theorem gc68_gDeg1Connector_of_ogReroute (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g)
    (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (h : gc68_OGReroute ends K o x y g) :
    gc65_GDeg1Connector ends K o x y g :=
  gc66_gDeg1Connector_of_removalSurvival ends hnd K hxg
    (gc68_removalSurvival_of_ogReroute ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc h)





theorem gc68_countIneq_of_ogReroute (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (h : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
        gc68_OGReroute ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc66_countIneq_of_removalSurvival ends hnd hox hoy hog hxy hxg hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc68_removalSurvival_of_ogReroute ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc (h K hK)

end Abstract

open Classical









theorem gc68_witness_og_via (S : Finset (Fin 5)) {i : Fin 5}
    (hi : i ∈ S) (hi34 : i = 2 ∨ i = 3 ∨ i = 4) : connK gc59_witnessEnds S 0 3 := by
  refine Relation.ReflTransGen.single ⟨i, hi, ?_, ?_, ?_⟩ <;>
    rcases hi34 with rfl | rfl | rfl <;> decide




theorem gc68_witness_ogReroute :
    gc68_OGReroute gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  intro D hDV hDsrc hDmin L hL
  have hVeq : (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) := by
    decide
  
  have hle2 : #D ≤ 2 := by
    have := hDmin ({1, 2} : Finset (Fin 5)) (by rw [hVeq]; decide) gc59_witnessEnds_D_sources
    simpa using this
  
  have hDcases : D = ({1, 2} : Finset (Fin 5)) ∨ D = ({1, 3} : Finset (Fin 5))
      ∨ D = ({1, 4} : Finset (Fin 5)) := by
    rw [hVeq] at hDV
    have hmem : D ∈ (({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
        (fun D => sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ #D ≤ 2)) := by
      rw [Finset.mem_filter, Finset.mem_powerset]; exact ⟨hDV, hDsrc, hle2⟩
    have hset : (({1, 2, 3, 4} : Finset (Fin 5)).powerset.filter
        (fun D => sources gc59_witnessEnds D = ({2, 3} : Finset (Fin 4)) ∧ #D ≤ 2))
        = ({({1, 2} : Finset (Fin 5)), ({1, 3} : Finset (Fin 5)),
            ({1, 4} : Finset (Fin 5))} : Finset (Finset (Fin 5))) := by decide
    rw [hset] at hmem
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hmem
  rw [gc59_witness_LblockSet] at hL
  simp only [Finset.mem_insert, Finset.mem_singleton] at hL
  
  rcases hDcases with rfl | rfl | rfl <;> rcases hL with rfl | rfl | rfl <;>
    first
    | (refine gc68_witness_og_via _ (i := 2) ?_ (by decide); decide)
    | (refine gc68_witness_og_via _ (i := 3) ?_ (by decide); decide)
    | (refine gc68_witness_og_via _ (i := 4) ?_ (by decide); decide)


theorem gc68_witness_removalSurvival :
    gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc68_removalSurvival_of_ogReroute gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc59_witnessEnds_univ_sources gc59_witnessEnds_K_sources gc68_witness_ogReroute


theorem gc68_witness_gDeg1Connector :
    gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc68_gDeg1Connector_of_ogReroute gc59_witnessEnds gc59_witnessEnds_loopless _
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc59_witnessEnds_univ_sources gc59_witnessEnds_K_sources gc68_witness_ogReroute






theorem gc68_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L D : Finset ι) (o x g : W),
        o ≠ x → sources ends K = ({o, x} : Finset W) → D ⊆ univ \ K →
        (connK ends ((K ∪ L) \ D) x g ↔ connK ends ((K ∪ L) \ D) o g))
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ x → o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        sources ends K = ({o, x} : Finset W) →
        gc68_OGReroute ends K o x y g → gc66_GDeg1RemovalSurvival ends K o x y g)
    ∧ 
    gc68_OGReroute gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc66_GDeg1RemovalSurvival gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends hnd K L D o x g hox hKsrc hDV => gc68_xg_iff_og_survives ends hnd hox hKsrc hDV,
    fun ends hnd K o x y g hox hoy hog hxy hxg hyg huniv hKsrc h =>
      gc68_removalSurvival_of_ogReroute ends hnd K hox hoy hog hxy hxg hyg huniv hKsrc h,
    gc68_witness_ogReroute,
    gc68_witness_removalSurvival,
    gc68_witness_gDeg1Connector⟩

end StatMech.Walls
