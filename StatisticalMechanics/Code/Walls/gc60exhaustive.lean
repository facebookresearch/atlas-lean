/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



































































import Mathlib
import Code.Walls.gc59residual

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





theorem gc60_degK_mono (ends : ι → Sym2 W) {S T : Finset ι} (hST : S ⊆ T) (g : W) :
    degK ends S g ≤ degK ends T g :=
  Finset.card_le_card (Finset.filter_subset_filter _ hST)





theorem gc60_degK_zero_of_even (ends : ι → Sym2 W) {g : W} (hg1 : degK ends (univ : Finset ι) g = 1)
    {S : Finset ι} (hSeven : Even (degK ends S g)) : degK ends S g = 0 := by
  have hle : degK ends S g ≤ 1 := hg1 ▸ gc60_degK_mono ends (Finset.subset_univ S) g
  interval_cases h : degK ends S g
  · rfl
  · exact absurd hSeven (by simp)


theorem gc60_no_gEdge_of_degZero (ends : ι → Sym2 W) {S : Finset ι} {g : W}
    (hS0 : degK ends S g = 0) : ∀ i ∈ S, g ∉ ends i := by
  intro i hiS hgi
  have : i ∈ S.filter (fun j => g ∈ ends j) := Finset.mem_filter.2 ⟨hiS, hgi⟩
  rw [degK, Finset.card_eq_zero] at hS0
  simp [hS0] at this




theorem gc60_not_connK_of_isolated (ends : ι → Sym2 W) {S : Finset ι} {x g : W}
    (hxg : x ≠ g) (hiso : ∀ i ∈ S, g ∉ ends i) : ¬ connK ends S x g := by
  intro h
  
  have hgx : connK ends S g x := connK_symm ends S h
  rcases hgx.cases_head with hrefl | ⟨c, hstep, _⟩
  · exact hxg hrefl.symm
  · obtain ⟨i, hiS, hg, _, _⟩ := hstep
    exact hiso i hiS hg





theorem gc60_isolated_of_gDegOne (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (hog : o ≠ g) (hxg : x ≠ g) (hKsrc : sources ends K = ({o, x} : Finset W))
    (hg1 : degK ends (univ : Finset ι) g = 1) {L : Finset ι} (hLsrc : sources ends L = (∅ : Finset W)) :
    ∀ i ∈ K ∪ L, g ∉ ends i := by
  
  have hKeven : Even (degK ends K g) := by
    rw [← Nat.not_odd_iff_even, ← mem_sources, hKsrc]
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hog h.symm
    · exact hxg h.symm
  have hLeven : Even (degK ends L g) := by
    rw [← Nat.not_odd_iff_even, ← mem_sources, hLsrc]; simp
  have hK0 : degK ends K g = 0 := gc60_degK_zero_of_even ends hg1 hKeven
  have hL0 : degK ends L g = 0 := gc60_degK_zero_of_even ends hg1 hLeven
  intro i hi hgi
  rw [Finset.mem_union] at hi
  rcases hi with hiK | hiL
  · exact gc60_no_gEdge_of_degZero ends hK0 i hiK hgi
  · exact gc60_no_gEdge_of_degZero ends hL0 i hiL hgi






theorem gc60_lblockSet_empty_of_gDegOne (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (hog : o ≠ g) (hxg : x ≠ g) (hKsrc : sources ends K = ({o, x} : Finset W))
    (hg1 : degK ends (univ : Finset ι) g = 1) :
    gc51_LblockSet ends K o x g = (∅ : Finset (Finset ι)) := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro L hL
  rw [gc51_LblockSet, Finset.mem_filter, Finset.mem_powerset] at hL
  obtain ⟨hLV, hLsrc, hgate⟩ := hL
  exact gc60_not_connK_of_isolated ends hxg
    (gc60_isolated_of_gDegOne ends K hog hxg hKsrc hg1 (y := y) hLsrc) hgate












theorem gc60_disjointConnector_of_gDegOne (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hg1 : degK ends (univ : Finset ι) g = 1) :
    gc57_DisjointConnector ends K o x y g := by
  obtain ⟨D, hDV, hDsrc⟩ := gc53_exists_fixedPath ends hnd K hoy hog hxy hxg hyg huniv hKsrc
  apply gc57_disjointConnector_of_disjoint ends K hDV hDsrc
  intro L hL
  rw [gc60_lblockSet_empty_of_gDegOne ends K (y := y) hog hxg hKsrc hg1] at hL
  exact absurd hL (Finset.notMem_empty L)

















theorem gc60_cover_of_gateOr (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
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
      ∨ gc59_RerouteConnector ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  rcases hcov with hxg | hg1 | hyge | hdisj | hreroute
  · exact gc58_disjointConnector_of_gateInK_exists ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hxg
  · exact gc60_disjointConnector_of_gDegOne ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hg1
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inl hyge))
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inr hdisj))
  · exact gc59_disjointConnector_of_reroute ends K hreroute






theorem gc60_countIneq_of_cover (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      (connK ends K x g)
      ∨ (degK ends (univ : Finset ι) g = 1)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc59_RerouteConnector ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg' hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc60_cover_of_gateOr ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (hcov K hK)





theorem gc60_gDeg_univ_odd (ends : ι → Sym2 W) {o x y g : W}
    (hog : o ≠ g) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    Odd (degK ends (univ : Finset ι) g) := by
  rw [← mem_sources, huniv]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto









theorem gc60_gDeg_dichotomy (ends : ι → Sym2 W) {o x y g : W}
    (hog : o ≠ g) (hxg : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W)) :
    degK ends (univ : Finset ι) g = 1 ∨ 3 ≤ degK ends (univ : Finset ι) g := by
  have hodd : Odd (degK ends (univ : Finset ι) g) := gc60_gDeg_univ_odd ends hog hxg hyg huniv
  obtain ⟨k, hk⟩ := hodd
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · exact Or.inl (by omega)
  · exact Or.inr (by omega)






theorem gc60_cover_reduce_to_parallelG (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hpar : 3 ≤ degK ends (univ : Finset ι) g →
      (connK ends K x g)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc59_RerouteConnector ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  rcases gc60_gDeg_dichotomy ends hog hxg' hyg huniv with hg1 | hge3
  · exact gc60_disjointConnector_of_gDegOne ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hg1
  · rcases hpar hge3 with hxg | hyge | hdisj | hreroute
    · exact gc58_disjointConnector_of_gateInK_exists ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hxg
    · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inl hyge))
    · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inr hdisj))
    · exact gc59_disjointConnector_of_reroute ends K hreroute

end Abstract

open Classical















noncomputable def gc60_witnessEnds : Fin 3 → Sym2 (Fin 4) :=
  ![s(0, 1), s(0, 2), s(0, 3)]


theorem gc60_witnessEnds_univ_sources :
    sources gc60_witnessEnds (univ : Finset (Fin 3)) = ({0, 1, 2, 3} : Finset (Fin 4)) := by decide


theorem gc60_witnessEnds_K_sources :
    sources gc60_witnessEnds ({0} : Finset (Fin 3)) = ({0, 1} : Finset (Fin 4)) := by decide


theorem gc60_witnessEnds_loopless : ∀ i : Fin 3, ¬ (gc60_witnessEnds i).IsDiag := by decide


theorem gc60_witnessEnds_gDegOne :
    degK gc60_witnessEnds (univ : Finset (Fin 3)) (3 : Fin 4) = 1 := by decide


theorem gc60_witness_not_gateInK :
    ¬ connK gc60_witnessEnds ({0} : Finset (Fin 3)) 1 3 := by
  intro h
  have inv : ∀ w : Fin 4, connK gc60_witnessEnds ({0} : Finset (Fin 3)) 1 w → (w = 0 ∨ w = 1) := by
    intro w hw
    induction hw with
    | refl => decide
    | @tail b c _ hstep ih =>
      obtain ⟨i, hi, hbi, hci, hbc⟩ := hstep
      rcases ih with rfl | rfl <;> (fin_cases hi <;> revert hbc hbi hci <;> revert c <;> decide)
  rcases inv 3 h with h3 | h3 <;> exact absurd h3 (by decide)



theorem gc60_witness_lblock_empty :
    gc51_LblockSet gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 3 = (∅ : Finset (Finset (Fin 3))) :=
  gc60_lblockSet_empty_of_gDegOne gc60_witnessEnds ({0} : Finset (Fin 3)) (y := 2)
    (by decide) (by decide) gc60_witnessEnds_K_sources gc60_witnessEnds_gDegOne






theorem gc60_witness_disjointConnector :
    gc57_DisjointConnector gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 2 3 :=
  gc60_disjointConnector_of_gDegOne gc60_witnessEnds gc60_witnessEnds_loopless ({0} : Finset (Fin 3))
    (by decide) (by decide) (by decide) (by decide) (by decide)
    gc60_witnessEnds_univ_sources gc60_witnessEnds_K_sources gc60_witnessEnds_gDegOne



theorem gc60_witness_no_ygEdge :
    ¬ ∃ i, i ∈ (univ : Finset (Fin 3)) \ ({0} : Finset (Fin 3)) ∧ gc60_witnessEnds i = s(2, 3) := by
  decide


































theorem gc60_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W),
        o ≠ y → o ≠ g → x ≠ y → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
        sources ends K = ({o, x} : Finset W) →
        degK ends (univ : Finset ι) g = 1 →
          gc57_DisjointConnector ends K o x y g)
    ∧ (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (o x y g : W),
        o ≠ g → x ≠ g → y ≠ g →
        sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W) →
          degK ends (univ : Finset ι) g = 1 ∨ 3 ≤ degK ends (univ : Finset ι) g)
    ∧ gc51_LblockSet gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 3 = (∅ : Finset (Finset (Fin 3)))
    ∧ gc57_DisjointConnector gc60_witnessEnds ({0} : Finset (Fin 3)) 0 1 2 3 :=
  ⟨fun ends hnd K o x y g hoy hog hxy hxg hyg huniv hKsrc hg1 =>
      gc60_disjointConnector_of_gDegOne ends hnd K hoy hog hxy hxg hyg huniv hKsrc hg1,
    fun ends o x y g hog hxg hyg huniv => gc60_gDeg_dichotomy ends hog hxg hyg huniv,
    gc60_witness_lblock_empty,
    gc60_witness_disjointConnector⟩

end StatMech.Walls
