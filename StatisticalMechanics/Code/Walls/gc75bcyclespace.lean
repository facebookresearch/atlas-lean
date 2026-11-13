/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































































import Mathlib
import Code.Walls.gc74bbridge
import Code.Walls.gc65cyclespace
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

















theorem gc75b_disjoint_iff_gEdge_and_rest {P D : Finset ι} {eD : ι} (heD : eD ∈ D) :
    Disjoint P D ↔ eD ∉ P ∧ Disjoint P (D \ ({eD} : Finset ι)) := by
  constructor
  · intro hPD
    refine ⟨fun hmem => Finset.disjoint_left.1 hPD hmem heD, ?_⟩
    exact Finset.disjoint_of_subset_right Finset.sdiff_subset hPD
  · rintro ⟨heDP, hrest⟩
    rw [Finset.disjoint_left]
    intro i hiP hiD
    by_cases h : i = eD
    · subst h; exact heDP hiP
    · exact Finset.disjoint_left.1 hrest hiP (Finset.mem_sdiff.2 ⟨hiD, by
        simp only [Finset.mem_singleton]; exact h⟩)




theorem gc75b_survives_of_disjoint (ends : ι → Sym2 W)
    {K L D P : Finset ι} {o g : W}
    (hPG : P ⊆ K ∪ L) (hPD : Disjoint P D) (hPconn : connK ends P o g) :
    connK ends ((K ∪ L) \ D) o g :=
  mng_connK_of_disjoint ends hPG hPD hPconn















theorem gc75b_disjointConnector_iff_survives (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) {K L D : Finset ι} {o g : W} (hog : o ≠ g) :
    (∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g)
      ↔ connK ends ((K ∪ L) \ D) o g :=
  gc72_leafClause_iff_survives ends hnd hog






theorem gc75b_bridgeConnectors_iff_notCut (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hog : o ≠ g) {D : Finset ι} :
    (∀ L ∈ gc51_LblockSet ends K o x g,
        ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g)
      ↔ (∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) := by
  constructor
  · intro h L hL
    exact (gc75b_disjointConnector_iff_survives ends hnd hog).1 (h L hL)
  · intro h L hL
    exact (gc75b_disjointConnector_iff_survives ends hnd hog).2 (h L hL)









theorem gc75b_bridgeConnectors (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hog : o ≠ g)
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hconn : ∀ L ∈ gc51_LblockSet ends K o x g,
        ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W) ∧ Disjoint P D ∧ connK ends P o g) :
    gc71_TwoCommodityLeaf ends K o x y g :=
  gc74b_twoCommodityLeaf_of_bridgeConnectors ends hnd K hog hDV hDsrc hD1 hconn





theorem gc75b_bridgeConnectors_of_notCut (ends : ι → Sym2 W)
    (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) {o x y g : W} (hog : o ≠ g)
    {D : Finset ι} (hDV : D ⊆ univ \ K) (hDsrc : sources ends D = ({y, g} : Finset W))
    (hD1 : degK ends D g = 1)
    (hnotcut : ∀ L ∈ gc51_LblockSet ends K o x g, connK ends ((K ∪ L) \ D) o g) :
    gc71_TwoCommodityLeaf ends K o x y g :=
  gc73b_twoCommodityLeaf_of_notCut ends hnd K hog hDV hDsrc hD1 hnotcut













theorem gc75b_room_survives (ends : ι → Sym2 W) {D : Finset ι} {y g : W}
    (hge3 : 3 ≤ degK ends (univ : Finset ι) g)
    (hDsrc : sources ends D = ({y, g} : Finset W)) (hD1 : degK ends D g = 1) :
    2 ≤ degK ends ((univ : Finset ι) \ D) g :=
  gc65_gDegGe3_room ends hge3 hD1

end Abstract

open Classical












theorem gc75b_brEnds2_P_src :
    sources gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4)) := by decide


theorem gc75b_brEnds2_P_conn :
    connK gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) 0 3 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).tail
    ⟨2, by decide, by decide, by decide, by decide⟩



theorem gc75b_brEnds2_disjoint_P123 :
    ({0, 2} : Finset (Fin 5)) ⊆ (({0} : Finset (Fin 5)) ∪ ({1, 2, 3} : Finset (Fin 5)))
      ∧ sources gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4))
      ∧ Disjoint ({0, 2} : Finset (Fin 5)) ({3} : Finset (Fin 5))
      ∧ connK gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) 0 3 :=
  ⟨by decide, gc75b_brEnds2_P_src, by decide, gc75b_brEnds2_P_conn⟩



theorem gc75b_brEnds2_disjoint_P124 :
    ({0, 2} : Finset (Fin 5)) ⊆ (({0} : Finset (Fin 5)) ∪ ({1, 2, 4} : Finset (Fin 5)))
      ∧ sources gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) = ({0, 3} : Finset (Fin 4))
      ∧ Disjoint ({0, 2} : Finset (Fin 5)) ({3} : Finset (Fin 5))
      ∧ connK gc74b_brEnds2 ({0, 2} : Finset (Fin 5)) 0 3 :=
  ⟨by decide, gc75b_brEnds2_P_src, by decide, gc75b_brEnds2_P_conn⟩







theorem gc75b_brEnds2_twoCommodityLeaf :
    gc71_TwoCommodityLeaf gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 2 3 := by
  refine gc75b_bridgeConnectors gc74b_brEnds2 gc74b_brEnds2_loopless ({0} : Finset (Fin 5))
    (by decide) gc74b_brEnds2_goodD_data.1 gc74b_brEnds2_goodD_data.2.1
    gc74b_brEnds2_goodD_data.2.2 ?_
  intro L hL
  rw [gc74b_brEnds2_LblockSet] at hL
  simp only [Finset.mem_insert, Finset.mem_singleton] at hL
  rcases hL with rfl | rfl
  · exact ⟨({0, 2} : Finset (Fin 5)), gc75b_brEnds2_disjoint_P123.1, gc75b_brEnds2_disjoint_P123.2.1,
      gc75b_brEnds2_disjoint_P123.2.2.1, gc75b_brEnds2_disjoint_P123.2.2.2⟩
  · exact ⟨({0, 2} : Finset (Fin 5)), gc75b_brEnds2_disjoint_P124.1, gc75b_brEnds2_disjoint_P124.2.1,
      gc75b_brEnds2_disjoint_P124.2.2.1, gc75b_brEnds2_disjoint_P124.2.2.2⟩










theorem gc75b_status :
    
    (∀ {ι : Type*} [DecidableEq ι] [Fintype ι] (P D : Finset ι) (eD : ι),
        eD ∈ D → (Disjoint P D ↔ eD ∉ P ∧ Disjoint P (D \ ({eD} : Finset ι))))
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K L D : Finset ι) (o g : W),
        o ≠ g →
        ((∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W)
              ∧ Disjoint P D ∧ connK ends P o g)
          ↔ connK ends ((K ∪ L) \ D) o g))
    ∧ 
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag) (K : Finset ι) (o x y g : W)
      (D : Finset ι),
        o ≠ g → D ⊆ univ \ K → sources ends D = ({y, g} : Finset W) → degK ends D g = 1 →
        (∀ L ∈ gc51_LblockSet ends K o x g,
          ∃ P, P ⊆ K ∪ L ∧ sources ends P = ({o, g} : Finset W)
            ∧ Disjoint P D ∧ connK ends P o g) →
        gc71_TwoCommodityLeaf ends K o x y g)
    ∧ 
    gc71_TwoCommodityLeaf gc74b_brEnds2 ({0} : Finset (Fin 5)) 0 1 2 3 :=
  ⟨fun P D eD heD => gc75b_disjoint_iff_gEdge_and_rest heD,
    fun ends hnd K L D o g hog => gc75b_disjointConnector_iff_survives ends hnd hog,
    fun ends hnd K o x y g D hog hDV hDsrc hD1 hconn =>
      gc75b_bridgeConnectors ends hnd K hog hDV hDsrc hD1 hconn,
    gc75b_brEnds2_twoCommodityLeaf⟩

end StatMech.Walls
