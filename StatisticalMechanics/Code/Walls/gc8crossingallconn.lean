/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





















































































import Mathlib
import Code.Sharpness.Switching
import Code.Sharpness.SwitchingDichotomy
import Code.Sharpness.DeltaRewrite
import Code.Sharpness.DeltaRewriteDichotomy
import Code.Walls.gc7core
import Code.Walls.gc7ghosteven

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FieldGhostDict

variable {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V] [Fintype V]













def gc8_disconn (ends : ι → Sym2 V) (o g : V) (m : Finset ι) : Prop :=
  ¬ connK ends m o g




def gc8_caseA (ends : ι → Sym2 V) (o x y g : V) (m : Finset ι) : Prop :=
  (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g)




def gc8_caseB (ends : ι → Sym2 V) (o x y g : V) (m : Finset ι) : Prop :=
  (¬ connK ends m o g) ∧ (connK ends m o y ∧ connK ends m x g)








theorem gc8_caseB_eq_swap (ends : ι → Sym2 V) (o x y g : V) (m : Finset ι) :
    gc8_caseB ends o x y g m = gc8_caseA ends o y x g m := rfl










theorem gc8_four_marks_even (o x y : V) (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y) :
    Even (insert (none : Option V) (({o, x, y} : Finset V).map someEmb)).card :=
  gc7_combined_source_even o x y hox hoy hxy



















theorem gc8_caseA_caseB_disjoint (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g}) :
    ¬ (gc8_caseA ends o x y g m ∧ gc8_caseB ends o x y g m) := by
  rintro ⟨⟨hdisc, hox', _hyg'⟩, ⟨_, hoy', _hxg'⟩⟩
  
  have hprop := disconnect_dichotomy_prop ends m hnd hox hoy hog hxy hxg hyg hsrc hdisc
  exact hprop.mp ⟨hox', _hyg'⟩ ⟨hoy', _hxg'⟩










theorem gc8_disconn_eq_union (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g}) :
    gc8_disconn ends o g m ↔ (gc8_caseA ends o x y g m ∨ gc8_caseB ends o x y g m) := by
  constructor
  · intro hdisc
    
    rcases disconnect_dichotomy ends m hnd hox hoy hog hxy hxg hyg hsrc hdisc with hA | hB
    · exact Or.inl ⟨hdisc, hA⟩
    · exact Or.inr ⟨hdisc, hB⟩
  · rintro (⟨hdisc, _⟩ | ⟨hdisc, _⟩) <;> exact hdisc











theorem gc8_disconn_indicator_split (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g}) :
    (if gc8_disconn ends o g m then (1 : ℝ) else 0)
      = (if gc8_disconn ends o g m ∧ (connK ends m o x ∧ connK ends m y g) then 1 else 0)
        + (if gc8_disconn ends o g m ∧ (connK ends m o y ∧ connK ends m x g) then 1 else 0) := by
  
  have hdich : gc8_disconn ends o g m →
      ((connK ends m o x ∧ connK ends m y g) ↔ ¬ (connK ends m o y ∧ connK ends m x g)) := by
    intro hdisc
    exact disconnect_dichotomy_prop ends m hnd hox hoy hog hxy hxg hyg hsrc hdisc
  exact sdr_deltaIndicator_split hdich


















theorem gc8_delta_eq_caseA_plus_caseB (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)
      = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
        + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) :=
  drd_deltaRewrite_full ends F hox hoy hog hxy hxg hyg hnd hsrcSet










theorem gc8_caseB_pairSum_eq_swap (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V) :
    drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m)
      = drd_pairSum ends ({o, y, x, g} : Finset V) F (fun m => gc8_caseA ends o y x g m) := by
  
  have hset : ({o, x, y, g} : Finset V) = ({o, y, x, g} : Finset V) := by
    ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hpred : (fun m : Finset ι => gc8_caseB ends o x y g m)
      = (fun m : Finset ι => gc8_caseA ends o y x g m) := by
    funext m; exact gc8_caseB_eq_swap ends o x y g m
  rw [hset, hpred]






























theorem gc8_crossingAllConn (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    
    (∀ m : Finset ι, gc8_caseB ends o x y g m = gc8_caseA ends o y x g m)
    
    ∧ (∀ m : Finset ι, (∀ i ∈ m, ¬ (ends i).IsDiag) → sources ends m = {o, x, y, g} →
        ¬ (gc8_caseA ends o x y g m ∧ gc8_caseB ends o x y g m))
    
    ∧ (∀ m : Finset ι, (∀ i ∈ m, ¬ (ends i).IsDiag) → sources ends m = {o, x, y, g} →
        (gc8_disconn ends o g m ↔ (gc8_caseA ends o x y g m ∨ gc8_caseB ends o x y g m)))
    
    ∧ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)
        = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
          + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro m; exact gc8_caseB_eq_swap ends o x y g m
  · intro m hndm hsrcm
    exact gc8_caseA_caseB_disjoint ends m hndm o x y g hox hoy hog hxy hxg hyg hsrcm
  · intro m hndm hsrcm
    exact gc8_disconn_eq_union ends m hndm o x y g hox hoy hog hxy hxg hyg hsrcm
  · exact gc8_delta_eq_caseA_plus_caseB ends F hox hoy hog hxy hxg hyg hnd hsrcSet
















theorem gc8_pathCrossing_input (ends : ι → Sym2 V) (m : Finset ι)
    (hnd : ∀ i ∈ m, ¬ (ends i).IsDiag) (o x y g : V)
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources ends m = {o, x, y, g})
    (hdisc : ¬ connK ends m o g) :
    ((connK ends m o x ∧ connK ends m y g) ∨ (connK ends m o y ∧ connK ends m x g))
      ∧ ¬ ((connK ends m o x ∧ connK ends m y g) ∧ (connK ends m o y ∧ connK ends m x g)) :=
  gc7_core_pathCrossing_dichotomy ends m hnd o x y g hox hoy hog hxy hxg hyg hsrc hdisc












theorem gc8_crossingAllConn_nonvacuous :
    let ends : Fin 2 → Sym2 (Fin 4) := witEnds
    sources ends witM = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ gc8_caseA ends (0 : Fin 4) 1 2 3 witM
      ∧ ¬ gc8_caseB ends (0 : Fin 4) 1 2 3 witM := by
  intro ends
  refine ⟨witM_sources, ⟨witM_not_connK_og, witM_connK_ox, witM_connK_yg⟩, ?_⟩
  
  rintro ⟨hdisc, ho2, h13⟩
  have hdisj := gc8_caseA_caseB_disjoint witEnds witM witEnds_not_diag (0 : Fin 4) 1 2 3
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) witM_sources
  exact hdisj ⟨⟨witM_not_connK_og, witM_connK_ox, witM_connK_yg⟩, ⟨hdisc, ho2, h13⟩⟩

end StatMech.Walls
