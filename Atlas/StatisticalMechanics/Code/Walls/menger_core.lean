/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































import Mathlib
import Code.Sharpness.Switching

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

open StatMech.Sharpness.RandomCurrent (sources connK connK_symm adjStep degK compOf
  sources_symmDiff mem_sources path_exists exists_conn_set)

section Abstract

open Classical

variable {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]




theorem mng_connK_mono (ends : ι → Sym2 W) {K₁ K₂ : Finset ι} (h : K₁ ⊆ K₂) {a b : W}
    (hab : connK ends K₁ a b) : connK ends K₂ a b := by
  refine Relation.ReflTransGen.mono ?_ hab
  rintro p q ⟨i, hi, hp, hq, hpq⟩
  exact ⟨i, h hi, hp, hq, hpq⟩





theorem mng_connK_of_disjoint (ends : ι → Sym2 W) {P G D : Finset ι}
    (hPG : P ⊆ G) (hPD : Disjoint P D) {a b : W} (hab : connK ends P a b) :
    connK ends (G \ D) a b := by
  have hsub : P ⊆ G \ D := by
    intro i hi
    rw [Finset.mem_sdiff]
    exact ⟨hPG hi, Finset.disjoint_left.1 hPD hi⟩
  exact mng_connK_mono ends hsub hab










theorem mng_connK_of_sources (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    (P : Finset ι) {a b : W} (hab : a ≠ b) (hP : sources ends P = ({a, b} : Finset W)) :
    connK ends P a b := by
  apply path_exists ends P (fun i _ => hnd i) a b
  · rw [← mem_sources, hP]; simp
  · intro z hz; rw [← mem_sources, hP] at hz; simpa using hz
  · exact hab




theorem mng_sources_symmDiff_cycle (ends : ι → Sym2 W) {P C : Finset ι} {a b : W}
    (hP : sources ends P = ({a, b} : Finset W)) (hC : sources ends C = (∅ : Finset W)) :
    sources ends (P ∆ C) = ({a, b} : Finset W) := by
  rw [sources_symmDiff, hP, hC]; simp




theorem mng_symmDiff_connector (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {P C : Finset ι} {a b : W} (hab : a ≠ b)
    (hP : sources ends P = ({a, b} : Finset W)) (hC : sources ends C = (∅ : Finset W)) :
    connK ends (P ∆ C) a b :=
  mng_connK_of_sources ends hnd (P ∆ C) hab (mng_sources_symmDiff_cycle ends hP hC)













theorem mng_exists_connector (ends : ι → Sym2 W) {G : Finset ι} {a b : W}
    (hab : connK ends G a b) (hne : a ≠ b) :
    ∃ P, P ⊆ G ∧ sources ends P = ({a, b} : Finset W) :=
  exists_conn_set ends G hab hne









theorem mng_two_disjoint_connectors (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {a b : W} (hne : a ≠ b) (hab : connK ends G a b)
    (hab2 : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({a, b} : Finset W) →
        connK ends (G \ P₁) a b) :
    ∃ P₁ P₂ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ Disjoint P₁ P₂ ∧
      sources ends P₁ = ({a, b} : Finset W) ∧ sources ends P₂ = ({a, b} : Finset W) ∧
      connK ends P₁ a b ∧ connK ends P₂ a b := by
  obtain ⟨P₁, hP₁G, hP₁src⟩ := mng_exists_connector ends hab hne
  have hab2' : connK ends (G \ P₁) a b := hab2 P₁ hP₁G hP₁src
  obtain ⟨P₂, hP₂GP, hP₂src⟩ := mng_exists_connector ends hab2' hne
  have hP₂G : P₂ ⊆ G := fun i hi => (Finset.mem_sdiff.1 (hP₂GP hi)).1
  have hdisj : Disjoint P₁ P₂ := by
    rw [Finset.disjoint_right]
    intro i hi
    exact (Finset.mem_sdiff.1 (hP₂GP hi)).2
  refine ⟨P₁, P₂, hP₁G, hP₂G, hdisj, hP₁src, hP₂src, ?_, ?_⟩
  · exact mng_connK_of_sources ends hnd P₁ hne hP₁src
  · exact mng_connK_of_sources ends hnd P₂ hne hP₂src














theorem mng_disjoint_connectors_of_pairwise (ends : ι → Sym2 W) {P G D : Finset ι}
    (hPG : P ⊆ G) (hPD : Disjoint P D) {x g : W} (hxg : connK ends P x g) :
    connK ends (G \ D) x g :=
  mng_connK_of_disjoint ends hPG hPD hxg






theorem mng_avoidance_of_two_disjoint (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
    {G : Finset ι} {x g : W} (hne : x ≠ g) (hxg : connK ends G x g)
    (hxg2 : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({x, g} : Finset W) →
        connK ends (G \ P₁) x g) :
    ∃ P₁ P₂ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ Disjoint P₁ P₂ ∧
      connK ends P₂ x g ∧ ∀ D : Finset ι, D ⊆ P₁ → connK ends (G \ D) x g := by
  obtain ⟨P₁, P₂, hP₁G, hP₂G, hdisj, hP₁src, hP₂src, hP₁c, hP₂c⟩ :=
    mng_two_disjoint_connectors ends hnd hne hxg hxg2
  refine ⟨P₁, P₂, hP₁G, hP₂G, hdisj, hP₂c, ?_⟩
  intro D hDP₁
  
  have hP₂D : Disjoint P₂ D :=
    Finset.disjoint_of_subset_right hDP₁ hdisj.symm
  exact mng_connK_of_disjoint ends hP₂G hP₂D hP₂c

end Abstract








open Classical




noncomputable def mng_cyc : Fin 4 → Sym2 (Fin 4) := ![s(0, 1), s(1, 2), s(2, 3), s(3, 0)]


theorem mng_cyc_loopless : ∀ i : Fin 4, ¬ (mng_cyc i).IsDiag := by decide


theorem mng_cyc_univ_sources : sources mng_cyc (univ : Finset (Fin 4)) = (∅ : Finset (Fin 4)) := by
  decide


theorem mng_cyc_P1_sources :
    sources mng_cyc ({0, 1} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by decide


theorem mng_cyc_P2_sources :
    sources mng_cyc ({2, 3} : Finset (Fin 4)) = ({0, 2} : Finset (Fin 4)) := by decide


theorem mng_cyc_disjoint : Disjoint ({0, 1} : Finset (Fin 4)) ({2, 3} : Finset (Fin 4)) := by decide


theorem mng_cyc_P1_conn : connK mng_cyc ({0, 1} : Finset (Fin 4)) 0 2 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 4))
      ⟨0, by decide, by decide, by decide, by decide⟩).trans
    (Relation.ReflTransGen.single (b := (2 : Fin 4))
      ⟨1, by decide, by decide, by decide, by decide⟩)


theorem mng_cyc_P2_conn : connK mng_cyc ({2, 3} : Finset (Fin 4)) 0 2 :=
  (Relation.ReflTransGen.single (b := (3 : Fin 4))
      ⟨3, by decide, by decide, by decide, by decide⟩).trans
    (Relation.ReflTransGen.single (b := (2 : Fin 4))
      ⟨2, by decide, by decide, by decide, by decide⟩)





theorem mng_test_cycle_two_disjoint :
    ∃ P₁ P₂ : Finset (Fin 4),
      P₁ ⊆ (univ : Finset (Fin 4)) ∧ P₂ ⊆ (univ : Finset (Fin 4)) ∧ Disjoint P₁ P₂ ∧
      sources mng_cyc P₁ = ({0, 2} : Finset (Fin 4)) ∧
      sources mng_cyc P₂ = ({0, 2} : Finset (Fin 4)) ∧
      connK mng_cyc P₁ 0 2 ∧ connK mng_cyc P₂ 0 2 :=
  ⟨{0, 1}, {2, 3}, Finset.subset_univ _, Finset.subset_univ _, mng_cyc_disjoint,
    mng_cyc_P1_sources, mng_cyc_P2_sources, mng_cyc_P1_conn, mng_cyc_P2_conn⟩





noncomputable def mng_brg : Fin 2 → Sym2 (Fin 3) := ![s(0, 1), s(1, 2)]


theorem mng_brg_conn : connK mng_brg (univ : Finset (Fin 2)) 0 2 :=
  (Relation.ReflTransGen.single (b := (1 : Fin 3))
      ⟨0, by decide, by decide, by decide, by decide⟩).trans
    (Relation.ReflTransGen.single (b := (2 : Fin 3))
      ⟨1, by decide, by decide, by decide, by decide⟩)


theorem mng_brg_univ_sources :
    sources mng_brg (univ : Finset (Fin 2)) = ({0, 2} : Finset (Fin 3)) := by decide


theorem mng_brg_delete_eq :
    (univ : Finset (Fin 2)) \ (univ : Finset (Fin 2)) = (∅ : Finset (Fin 2)) := by decide


theorem mng_brg_empty_disconn : ¬ connK mng_brg (∅ : Finset (Fin 2)) 0 2 := by
  intro h
  have inv : ∀ w : Fin 3, connK mng_brg (∅ : Finset (Fin 2)) 0 w → w = 0 := by
    intro w hw
    induction hw with
    | refl => rfl
    | @tail b c _ hstep ih => obtain ⟨i, hi, _⟩ := hstep; simp at hi
  exact absurd (inv 2 h) (by decide)







theorem mng_test_bridge_no_two_disjoint :
    connK mng_brg (univ : Finset (Fin 2)) 0 2 ∧
    sources mng_brg (univ : Finset (Fin 2)) = ({0, 2} : Finset (Fin 3)) ∧
    ¬ connK mng_brg ((univ : Finset (Fin 2)) \ (univ : Finset (Fin 2))) 0 2 := by
  refine ⟨mng_brg_conn, mng_brg_univ_sources, ?_⟩
  rw [mng_brg_delete_eq]; exact mng_brg_empty_disconn






theorem mng_status :
    
    (∀ {ι W : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq W] [Fintype W]
      (ends : ι → Sym2 W) (hnd : ∀ i : ι, ¬ (ends i).IsDiag)
      {G : Finset ι} {a b : W} (hne : a ≠ b) (hab : connK ends G a b)
      (hab2 : ∀ P₁ : Finset ι, P₁ ⊆ G → sources ends P₁ = ({a, b} : Finset W) →
          connK ends (G \ P₁) a b),
      ∃ P₁ P₂ : Finset ι, P₁ ⊆ G ∧ P₂ ⊆ G ∧ Disjoint P₁ P₂ ∧
        sources ends P₁ = ({a, b} : Finset W) ∧ sources ends P₂ = ({a, b} : Finset W) ∧
        connK ends P₁ a b ∧ connK ends P₂ a b) ∧
    
    (∃ P₁ P₂ : Finset (Fin 4),
      P₁ ⊆ (univ : Finset (Fin 4)) ∧ P₂ ⊆ (univ : Finset (Fin 4)) ∧ Disjoint P₁ P₂ ∧
      connK mng_cyc P₁ 0 2 ∧ connK mng_cyc P₂ 0 2) ∧
    
    (¬ connK mng_brg ((univ : Finset (Fin 2)) \ (univ : Finset (Fin 2))) 0 2) :=
  ⟨fun ends hnd => mng_two_disjoint_connectors ends hnd,
   ⟨{0, 1}, {2, 3}, Finset.subset_univ _, Finset.subset_univ _, mng_cyc_disjoint,
     mng_cyc_P1_conn, mng_cyc_P2_conn⟩,
   by rw [mng_brg_delete_eq]; exact mng_brg_empty_disconn⟩

end StatMech.Walls
