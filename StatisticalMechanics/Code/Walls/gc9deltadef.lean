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
import Code.Walls.gc8crossingallconn
import Code.Walls.gc8core

open Finset BigOperators
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent
open StatMech.Sharpness.FieldGhostDict

variable {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V] [Fintype V]




















noncomputable def gc9_delta (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)





noncomputable def gc9_delta_caseA (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)




noncomputable def gc9_delta_caseB (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m)


















theorem gc9_delta_def (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    gc9_delta ends F o x y g
      = gc9_delta_caseA ends F o x y g + gc9_delta_caseB ends F o x y g :=
  gc8_delta_eq_caseA_plus_caseB ends F hox hoy hog hxy hxg hyg hnd hsrcSet











theorem gc9_delta_caseA_eq (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V) :
    gc9_delta_caseA ends F o x y g
      = drd_pairSum ends ({o, x, y, g} : Finset V) F
          (fun m => (¬ connK ends m o g) ∧ (connK ends m o x ∧ connK ends m y g)) := rfl











theorem gc9_delta_caseB_eq_swap (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V) :
    gc9_delta_caseB ends F o x y g = gc9_delta_caseA ends F o y x g := by
  unfold gc9_delta_caseB gc9_delta_caseA
  exact gc8_caseB_pairSum_eq_swap ends F o x y g











theorem gc9_delta_caseA_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V)
    (hF : ∀ m, 0 ≤ F m) :
    0 ≤ gc9_delta_caseA ends F o x y g :=
  gc8_core_pairSum_nonneg ends _ F _ hF


theorem gc9_delta_caseB_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V)
    (hF : ∀ m, 0 ≤ F m) :
    0 ≤ gc9_delta_caseB ends F o x y g :=
  gc8_core_pairSum_nonneg ends _ F _ hF







theorem gc9_delta_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (hF : ∀ m, 0 ≤ F m)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    0 ≤ gc9_delta ends F o x y g := by
  rw [gc9_delta_def ends F hox hoy hog hxy hxg hyg hnd hsrcSet]
  exact add_nonneg (gc9_delta_caseA_nonneg ends F o x y g hF)
    (gc9_delta_caseB_nonneg ends F o x y g hF)
























theorem gc9_deltaDef (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (hF : ∀ m, 0 ≤ F m)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    
    (gc9_delta ends F o x y g
        = gc9_delta_caseA ends F o x y g + gc9_delta_caseB ends F o x y g)
    
    ∧ (gc9_delta_caseB ends F o x y g = gc9_delta_caseA ends F o y x g)
    
    ∧ (0 ≤ gc9_delta ends F o x y g) := by
  refine ⟨?_, ?_, ?_⟩
  · exact gc9_delta_def ends F hox hoy hog hxy hxg hyg hnd hsrcSet
  · exact gc9_delta_caseB_eq_swap ends F o x y g
  · exact gc9_delta_nonneg ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet














theorem gc9_delta_def_consistent_pivotal (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)
      = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
        + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) :=
  gc8_core_delta_supported_allConn ends F hox hoy hog hxy hxg hyg hnd hsrcSet




theorem gc9_delta_nonneg_consistent_pivotal (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (hF : ∀ m, 0 ≤ F m)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) :=
  gc8_core_delta_nonneg ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet













theorem gc9_delta_def_nonvacuous :
    let ends : Fin 2 → Sym2 (Fin 4) := witEnds
    sources ends witM = ({0, 1, 2, 3} : Finset (Fin 4))
      ∧ gc8_caseA ends (0 : Fin 4) 1 2 3 witM
      ∧ ¬ gc8_caseB ends (0 : Fin 4) 1 2 3 witM :=
  gc8_crossingAllConn_nonvacuous

end StatMech.Walls
