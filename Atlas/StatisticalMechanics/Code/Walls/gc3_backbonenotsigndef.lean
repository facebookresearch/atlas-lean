/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/



















































































import Mathlib
import Code.Ising.AizenmanSignDominance
import Code.Ising.AizenmanInclusionExclusion
import Code.Ising.GHSDistinctSite

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness.RandomCurrent StatMech.Ising







variable {ι V : Type*} [DecidableEq ι] [DecidableEq V] [Fintype V] [Fintype ι]







theorem gc3_backbone_not_signDefinite (ends : ι → Sym2 V) (m₁ m₂ : Finset ι) {o x y : V}
    (h₁ : aie_allConn ends m₁ o x y) (h₂ : aie_noneConn ends m₂ o x y) :
    asd_ghsBackboneFactor ends m₁ o x y < 0
      ∧ 0 < asd_ghsBackboneFactor ends m₂ o x y :=
  asd_ghsBackboneFactor_not_signDefinite ends m₁ m₂ h₁ h₂















theorem gc3_qFactor_not_signDefinite {o x y : V} (hox : o ≠ x) (hxy : x ≠ y) :
    (∃ q : ConfigSpace V, ghsQFactor q o x y < 0)
      ∧ (∃ q : ConfigSpace V, 0 < ghsQFactor q o x y) :=
  ghsQFactor_not_signDefinite hox hxy

















theorem gc3_only_negative_cell_is_allConn (ends : ι → Sym2 V) (m : Finset ι) (o x y : V)
    (hneg : asd_ghsBackboneFactor ends m o x y < 0) :
    aie_allConn ends m o x y := by
  by_contra hnotall
  exact absurd (aie_backbone_factor_nonneg_not_all ends m hnotall) (not_le.mpr hneg)







theorem gc3_not_termwise_signDominance (ends : ι → Sym2 V) (m₁ m₂ : Finset ι) {o x y : V}
    (h₁ : aie_allConn ends m₁ o x y) (h₂ : aie_noneConn ends m₂ o x y) :
    (¬ ∀ m : Finset ι, asd_ghsBackboneFactor ends m o x y ≤ 0)
      ∧ (¬ ∀ m : Finset ι, 0 ≤ asd_ghsBackboneFactor ends m o x y) := by
  obtain ⟨hneg, hpos⟩ := gc3_backbone_not_signDefinite ends m₁ m₂ h₁ h₂
  refine ⟨?_, ?_⟩
  · intro hall; exact absurd (hall m₂) (not_le.mpr hpos)
  · intro hall; exact absurd (hall m₁) (not_le.mpr hneg)
















theorem gc3_connK_empty_eq (ends : ι → Sym2 V) {a b : V}
    (h : connK ends (∅ : Finset ι) a b) : a = b := by
  induction h with
  | refl => rfl
  | tail _ hstep ih =>
    obtain ⟨i, hi, _, _, _⟩ := hstep
    exact absurd hi (Finset.notMem_empty i)




theorem gc3_noneConn_empty (ends : ι → Sym2 V) {o x y : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    aie_noneConn ends (∅ : Finset ι) o x y :=
  ⟨fun h => hxy (gc3_connK_empty_eq ends h),
    fun h => hoy (gc3_connK_empty_eq ends h),
    fun h => hox (gc3_connK_empty_eq ends h)⟩






theorem gc3_allConn_concrete :
    aie_allConn (fun i : Fin 2 => if i = 0 then s((0 : Fin 3), 1) else s((1 : Fin 3), 2))
      ({0, 1} : Finset (Fin 2)) 0 1 2 := by
  set ends : Fin 2 → Sym2 (Fin 3) := fun i => if i = 0 then s((0 : Fin 3), 1) else s((1 : Fin 3), 2)
    with hends
  set m : Finset (Fin 2) := {0, 1} with hm
  
  have hox : connK ends m (0 : Fin 3) 1 := by
    apply Relation.ReflTransGen.single
    exact ⟨0, by rw [hm]; decide, by simp [hends], by simp [hends], by decide⟩
  
  have hxy : connK ends m (1 : Fin 3) 2 := by
    apply Relation.ReflTransGen.single
    exact ⟨1, by rw [hm]; decide, by simp [hends], by simp [hends], by decide⟩
  
  have hoy : connK ends m (0 : Fin 3) 2 := hox.trans hxy
  exact ⟨hxy, hoy, hox⟩







theorem gc3_backbone_not_signDefinite_concrete :
    asd_ghsBackboneFactor
        (fun i : Fin 2 => if i = 0 then s((0 : Fin 3), 1) else s((1 : Fin 3), 2))
        ({0, 1} : Finset (Fin 2)) 0 1 2 < 0
    ∧ 0 < asd_ghsBackboneFactor
        (fun i : Fin 2 => if i = 0 then s((0 : Fin 3), 1) else s((1 : Fin 3), 2))
        (∅ : Finset (Fin 2)) 0 1 2 := by
  refine ⟨?_, ?_⟩
  · obtain ⟨hxy, hoy, hox⟩ := gc3_allConn_concrete
    rw [asd_ghsBackboneFactor_allConn _ _ hxy hoy hox]; norm_num
  · obtain ⟨hxy, hoy, hox⟩ :=
      gc3_noneConn_empty (V := Fin 3) (o := 0) (x := 1) (y := 2)
        (fun i : Fin 2 => if i = 0 then s((0 : Fin 3), 1) else s((1 : Fin 3), 2))
        (by decide) (by decide) (by decide)
    rw [asd_ghsBackboneFactor_noConn _ _ hxy hoy hox]; norm_num
























theorem gc3_obstruction (ends : ι → Sym2 V) (m₁ m₂ : Finset ι) {o x y : V}
    (hox : o ≠ x) (hxy : x ≠ y) (h₁ : aie_allConn ends m₁ o x y)
    (h₂ : aie_noneConn ends m₂ o x y) :
    
    (asd_ghsBackboneFactor ends m₁ o x y = -2 ∧ asd_ghsBackboneFactor ends m₂ o x y = 1)
    
    ∧ (asd_ghsBackboneFactor ends m₁ o x y < 0 ∧ 0 < asd_ghsBackboneFactor ends m₂ o x y)
    
    ∧ (ghsQFactor (V := V) (fun _ => true) o x y = -2
        ∧ ghsQFactor (V := V) (fun z => decide (z ≠ x)) o x y = 2)
    
    ∧ ((∃ q : ConfigSpace V, ghsQFactor q o x y < 0)
        ∧ (∃ q : ConfigSpace V, 0 < ghsQFactor q o x y)) := by
  obtain ⟨hxy₁, hoy₁, hox₁⟩ := h₁
  obtain ⟨hxy₂, hoy₂, hox₂⟩ := h₂
  refine ⟨⟨?_, ?_⟩, ?_, ⟨?_, ?_⟩, ?_⟩
  · exact asd_ghsBackboneFactor_allConn ends m₁ hxy₁ hoy₁ hox₁
  · exact asd_ghsBackboneFactor_noConn ends m₂ hxy₂ hoy₂ hox₂
  · exact asd_ghsBackboneFactor_not_signDefinite ends m₁ m₂ ⟨hxy₁, hoy₁, hox₁⟩ ⟨hxy₂, hoy₂, hox₂⟩
  · exact ghsQFactor_const_one o x y
  · exact ghsQFactor_single_flip hox hxy
  · exact ghsQFactor_not_signDefinite hox hxy

end StatMech.Walls
