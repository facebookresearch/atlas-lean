/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Walls.gc57menger

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






theorem gc58_disjoint_K_of_subV {K D : Finset ι} (hDV : D ⊆ univ \ K) : Disjoint K D := by
  rw [Finset.disjoint_left]
  intro i hiK hiD
  exact (Finset.mem_sdiff.1 (hDV hiD)).2 hiK
















theorem gc58_disjointConnector_of_gateInK (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hxg : connK ends K x g) :
    gc57_DisjointConnector ends K o x y g := by
  refine ⟨D, hDV, hDsrc, ?_⟩
  intro L hL
  exact ⟨K, Finset.subset_union_left, gc58_disjoint_K_of_subV hDV, hxg⟩




theorem gc58_removalSurvival_of_gateInK (ends : ι → Sym2 W) (K : Finset ι) {o x y g : W}
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hxg : connK ends K x g) :
    gc55_RemovalSurvival ends K o x y g :=
  (gc57_disjointConnector_iff_removalSurvival_residue ends K).1
    (gc58_disjointConnector_of_gateInK ends K hDV hDsrc hxg)





theorem gc58_disjointConnector_of_gateInK_exists (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hxg : connK ends K x g) :
    gc57_DisjointConnector ends K o x y g := by
  obtain ⟨D, hDV, hDsrc⟩ :=
    gc53_exists_fixedPath ends hnd K hoy hog hxy hxg' hyg huniv hKsrc
  exact gc58_disjointConnector_of_gateInK ends K hDV hDsrc hxg



















theorem gc58_disjointConnector_tricho (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (K : Finset ι) {o x y g : W}
    (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hKsrc : sources ends K = ({o, x} : Finset W))
    (hcov :
      (connK ends K x g)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)) :
    gc57_DisjointConnector ends K o x y g := by
  rcases hcov with hxg | ⟨i, hiV, hi⟩ | ⟨D, hDV, hDsrc, hdisj⟩
  · exact gc58_disjointConnector_of_gateInK_exists ends hnd K hoy hog hxy hxg' hyg huniv hKsrc hxg
  · exact (gc57_disjointConnector_iff_removalSurvival_residue ends K).2
      (gc55_removalSurvival_of_ygEdge ends hnd K hyg hiV hi)
  · exact gc57_disjointConnector_of_disjoint ends K hDV hDsrc hdisj





theorem gc58_countIneq_of_tricho (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {o x y g : W} (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg' : x ≠ g) (hyg : y ≠ g)
    (huniv : sources ends (univ : Finset ι) = ({o, x, y, g} : Finset W))
    (hcov : ∀ K ∈ (univ : Finset ι).powerset.filter (fun K => sources ends K = ({o, x} : Finset W)),
      (connK ends K x g)
      ∨ (∃ i, i ∈ univ \ K ∧ ends i = s(y, g))
      ∨ (∃ D, D ⊆ univ \ K ∧ sources ends D = ({y, g} : Finset W)
            ∧ ∀ L ∈ gc51_LblockSet ends K o x g, Disjoint L D)) :
    gc39_ThreeColouringCountIneq ends o x y g := by
  apply gc57_countIneq_of_disjointConnector ends hnd hox hoy hog hxy hxg' hyg huniv
  intro K hK
  have hKsrc : sources ends K = ({o, x} : Finset W) := by
    simpa [Finset.mem_filter, Finset.mem_powerset] using hK
  exact gc58_disjointConnector_tricho ends hnd K hoy hog hxy hxg' hyg huniv hKsrc (hcov K hK)

end Abstract

open Classical










theorem gc58_witness_gateInK_K13 :
    connK gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 1 3 :=
  Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩


theorem gc58_witness_gateInK_K23 :
    connK gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 1 3 :=
  Relation.ReflTransGen.single ⟨3, by decide, by decide, by decide, by decide⟩




theorem gc58_witness_disjointConnector_K13 :
    gc57_DisjointConnector gc49_witnessEnds ({1, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc58_disjointConnector_of_gateInK gc49_witnessEnds _ (D := ({0, 2} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({1, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) from by decide]
  · decide
  · exact gc58_witness_gateInK_K13



theorem gc58_witness_disjointConnector_K23 :
    gc57_DisjointConnector gc49_witnessEnds ({2, 3} : Finset (Fin 4)) 0 1 2 3 := by
  apply gc58_disjointConnector_of_gateInK gc49_witnessEnds _ (D := ({0, 1} : Finset (Fin 4)))
  · rw [show (univ : Finset (Fin 4)) \ ({2, 3} : Finset (Fin 4)) = ({0, 1} : Finset (Fin 4)) from by decide]
  · decide
  · exact gc58_witness_gateInK_K23





theorem gc58_witness_cosetGateDom : gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3 := by
  apply gc55_cosetGateDom_of_removalSurvival
  intro K hK
  rw [gc50_witness_oxCurrents] at hK
  simp only [Finset.mem_insert, Finset.mem_singleton] at hK
  rcases hK with rfl | rfl
  · exact gc57_removalSurvival_of_disjointConnector gc49_witnessEnds _ gc58_witness_disjointConnector_K13
  · exact gc57_removalSurvival_of_disjointConnector gc49_witnessEnds _ gc58_witness_disjointConnector_K23



theorem gc58_witness_perKCount : gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  gc53_perKCount_of_cosetGateDom gc49_witnessEnds gc49_witnessEnds_loopless
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    gc49_witnessEnds_univ_sources gc58_witness_cosetGateDom

























theorem gc58_status :
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (K : Finset ι) (o x y g : W) (D : Finset ι),
        D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → connK ends K x g →
          gc57_DisjointConnector ends K o x y g)
    ∧ gc53_CosetGateDom gc49_witnessEnds (0 : Fin 4) 1 2 3
    ∧ gc52_PerKCount gc49_witnessEnds (0 : Fin 4) 1 2 3 :=
  ⟨fun ends K o x y g D hDV hDsrc hxg => gc58_disjointConnector_of_gateInK ends K hDV hDsrc hxg,
    gc58_witness_cosetGateDom, gc58_witness_perKCount⟩

end StatMech.Walls
