/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/










































































































import Mathlib
import Code.Walls.gc61parallelg
import Code.Walls.gc64twocommodity

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







theorem gc65_degK_add_sdiff (ends : ι → Sym2 W) (D : Finset ι) (g : W) :
    degK ends (univ : Finset ι) g = degK ends D g + degK ends ((univ : Finset ι) \ D) g := by
  unfold degK
  rw [← Finset.card_union_of_disjoint (Finset.disjoint_filter_filter (Finset.disjoint_sdiff))]
  congr 1
  ext i
  constructor
  · intro hi
    rw [Finset.mem_filter] at hi
    obtain ⟨-, hgi⟩ := hi
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_cases hiD : i ∈ D
    · exact Or.inl ⟨hiD, hgi⟩
    · exact Or.inr ⟨Finset.mem_sdiff.2 ⟨Finset.mem_univ _, hiD⟩, hgi⟩
  · intro hi
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter] at hi
    rw [Finset.mem_filter]
    rcases hi with ⟨-, hgi⟩ | ⟨-, hgi⟩ <;> exact ⟨Finset.mem_univ _, hgi⟩





theorem gc65_ygConnector_gDeg_odd (ends : ι → Sym2 W) {D : Finset ι} {y g : W}
    (hDsrc : sources ends D = ({y, g} : Finset W)) : Odd (degK ends D g) := by
  rw [← mem_sources, hDsrc]; simp






theorem gc65_gDegGe3_room (ends : ι → Sym2 W) {D : Finset ι} {g : W}
    (hge3 : 3 ≤ degK ends (univ : Finset ι) g) (hD1 : degK ends D g = 1) :
    2 ≤ degK ends ((univ : Finset ι) \ D) g := by
  have hadd := gc65_degK_add_sdiff ends D g
  omega





theorem gc65_room_of_gDeg1_ygConnector (ends : ι → Sym2 W) {D : Finset ι} {y g : W}
    (hge3 : 3 ≤ degK ends (univ : Finset ι) g)
    (hDsrc : sources ends D = ({y, g} : Finset W)) (hD1 : degK ends D g = 1) :
    2 ≤ degK ends ((univ : Finset ι) \ D) g :=
  gc65_gDegGe3_room ends hge3 hD1














def gc65_GDeg1Connector (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) : Prop :=
    ∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W) ∧ degK ends D g = 1
      ∧ ∀ L ∈ gc51_LblockSet ends K o x g,
          ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({x, g} : Finset W)
            ∧ Disjoint P D ∧ connK ends P x g




theorem gc65_disjointConnector_of_gDeg1Connector (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    (h : gc65_GDeg1Connector ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  obtain ⟨D, hDV, hDsrc, hD1, hL⟩ := h
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hLmem
  obtain ⟨P, hPG, hPsrc, hPD, hPconn⟩ := hL L hLmem
  exact ⟨P, hPG, hPD, hPconn⟩








theorem gc65_gDeg1Connector_of_data (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hL : ∀ L ∈ gc51_LblockSet ends K o x g,
        ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({x, g} : Finset W)
          ∧ Disjoint P D ∧ connK ends P x g) :
    gc65_GDeg1Connector ends K o x y g :=
  ⟨D, hDV, hDsrc, hD1, hL⟩






theorem gc65_trim_to_boundary (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {P G D : Finset ι} {x g : W} (hxg : x ≠ g)
    (hPG : P ⊆ G) (hPD : Disjoint P D) (hPconn : connK ends P x g) :
    ∃ P', P' ⊆ G ∧ sources ends P' = ({x, g} : Finset W) ∧ Disjoint P' D ∧ connK ends P' x g := by
  obtain ⟨P', hP'P, hP'src⟩ := exists_conn_set ends P hPconn hxg
  refine ⟨P', hP'P.trans hPG, hP'src, Finset.disjoint_of_subset_left hP'P hPD, ?_⟩
  apply path_exists ends P' (fun i _ => hnd i) x g
  · rw [← mem_sources, hP'src]; simp
  · intro z hz; rw [← mem_sources, hP'src] at hz; simpa using hz
  · exact hxg
















theorem gc65_disjointConnector_all (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
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
      ∨ gc65_GDeg1Connector ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  rcases hcov with hxg | hg1 | hyge | hdisj | hgd1
  · exact gc58_disjointConnector_of_gateInK_exists ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hxg
  · exact gc60_disjointConnector_of_gDegOne ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hg1
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inl hyge))
  · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inr hdisj))
  · exact gc65_disjointConnector_of_gDeg1Connector ends K hgd1




theorem gc65_countIneq_of_cover (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      (connK ends K x g)
      ∨ (degK ends (univ : Finset ι) g = 1)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc65_GDeg1Connector ends K o x y g) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg' hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc65_disjointConnector_all ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (hcov K hK)






theorem gc65_cover_reduce_to_parallelG (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hpar : 3 ≤ degK ends (univ : Finset ι) g →
      (connK ends K x g)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)
      ∨ gc65_GDeg1Connector ends K o x y g) :
    gc57_DisjointConnector ends K o x y g := by
  rcases gc60_gDeg_dichotomy ends hog hxg' hyg huniv with hg1 | hge3
  · exact gc60_disjointConnector_of_gDegOne ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hg1
  · rcases hpar hge3 with hxg | hyge | hdisj | hgd1
    · exact gc58_disjointConnector_of_gateInK_exists ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hxg
    · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inl hyge))
    · exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (Or.inr (Or.inr hdisj))
    · exact gc65_disjointConnector_of_gDeg1Connector ends K hgd1

end Abstract

open Classical



















theorem gc65_witness_gDeg :
    degK gc59_witnessEnds (univ : Finset (Fin 5)) (3 : Fin 4) = 3 := by decide


theorem gc65_witness_D_gDeg1 :
    degK gc59_witnessEnds ({1, 2} : Finset (Fin 5)) (3 : Fin 4) = 1 := by decide



theorem gc65_witness_room :
    2 ≤ degK gc59_witnessEnds ((univ : Finset (Fin 5)) \ ({1, 2} : Finset (Fin 5))) (3 : Fin 4) :=
  gc65_gDegGe3_room gc59_witnessEnds (by rw [gc65_witness_gDeg]) gc65_witness_D_gDeg1


theorem gc65_witness_P23_src :
    sources gc59_witnessEnds ({0, 3} : Finset (Fin 5)) = ({1, 3} : Finset (Fin 4)) := by decide


theorem gc65_witness_P24_src :
    sources gc59_witnessEnds ({0, 4} : Finset (Fin 5)) = ({1, 3} : Finset (Fin 4)) := by decide


theorem gc65_witness_P23_conn :
    connK gc59_witnessEnds ({0, 3} : Finset (Fin 5)) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc65_witness_P24_conn :
    connK gc59_witnessEnds ({0, 4} : Finset (Fin 5)) 1 3 :=
  (Relation.ReflTransGen.single (b := (0 : Fin 4)) ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨4, by decide, by decide, by decide, by decide⟩





theorem gc65_witness_gDeg1Connector :
    gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine ⟨({1, 2} : Finset (Fin 5)), ?_, gc59_witnessEnds_D_sources, gc65_witness_D_gDeg1, ?_⟩
  · rw [show (univ : Finset (Fin 5)) \ ({0} : Finset (Fin 5)) = ({1, 2, 3, 4} : Finset (Fin 5)) from by decide]
    decide
  · intro L hL
    rw [gc59_witness_LblockSet] at hL
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    · 
      refine ⟨({0, 3} : Finset (Fin 5)), ?_, gc65_witness_P23_src, by decide, gc65_witness_P23_conn⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({2, 3} : Finset (Fin 5))) = ({0, 2, 3} : Finset (Fin 5)) from by decide]
      decide
    · 
      refine ⟨({0, 4} : Finset (Fin 5)), ?_, gc65_witness_P24_src, by decide, gc65_witness_P24_conn⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({2, 4} : Finset (Fin 5))) = ({0, 2, 4} : Finset (Fin 5)) from by decide]
      decide
    · 
      refine ⟨({0, 3} : Finset (Fin 5)), ?_, gc65_witness_P23_src, by decide, gc65_witness_P23_conn⟩
      rw [show (({0} : Finset (Fin 5)) ∪ ({3, 4} : Finset (Fin 5))) = ({0, 3, 4} : Finset (Fin 5)) from by decide]
      decide



theorem gc65_witness_disjointConnector :
    gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  gc65_disjointConnector_of_gDeg1Connector gc59_witnessEnds _ gc65_witness_gDeg1Connector







theorem gc65_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (D : Finset ι) (y g : W),
        sources ends D = ({y, g} : Finset W) → Odd (degK ends D g))
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (D : Finset ι) (g : W),
        3 ≤ degK ends (univ : Finset ι) g → degK ends D g = 1 →
          2 ≤ degK ends ((univ : Finset ι) \ D) g)
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W),
        gc65_GDeg1Connector ends K o x y g → gc57_DisjointConnector ends K o x y g)
    ∧ 
    gc65_GDeg1Connector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3
    ∧ gc57_DisjointConnector gc59_witnessEnds ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun ends D y g h => gc65_ygConnector_gDeg_odd ends h,
    fun ends D g hge3 hD1 => gc65_gDegGe3_room ends hge3 hD1,
    fun ends K o x y g h => gc65_disjointConnector_of_gDeg1Connector ends K h,
    gc65_witness_gDeg1Connector,
    gc65_witness_disjointConnector⟩

end StatMech.Walls
