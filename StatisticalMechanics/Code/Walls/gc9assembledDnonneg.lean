/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




















































































import Mathlib
import Code.Walls.gc8core
import Code.Walls.gc8crossingallconn

open Finset BigOperators SimpleGraph
open scoped Sym2 symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]












theorem gc9_assembled_D_term_nonneg (J : Sym2 V → ℝ) (δ : V → V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hδ : ∀ x y, 0 ≤ δ x y) (x y : V) :
    0 ≤ J s(x, y) * δ x y :=
  mul_nonneg (hJ _) (hδ x y)













theorem gc9_assembled_D_nonneg (J : Sym2 V → ℝ) (δ : V → V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hδ : ∀ x y, 0 ≤ δ x y) :
    0 ≤ ∑ x : V, ∑ y : V, J s(x, y) * δ x y :=
  Finset.sum_nonneg fun x _ =>
    Finset.sum_nonneg fun y _ => gc9_assembled_D_term_nonneg J δ hJ hδ x y






theorem gc9_assembled_D_edges_nonneg (J : Sym2 V → ℝ) (δe : Sym2 V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hδ : ∀ e, 0 ≤ δe e) :
    0 ≤ ∑ e : Sym2 V, J e * δe e :=
  Finset.sum_nonneg fun e _ => mul_nonneg (hJ e) (hδ e)


















noncomputable def gc9_pivotalMass (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o g : V) (x y : V) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)






theorem gc9_concrete_delta_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    (hF : ∀ m, 0 ≤ F m) (o g x y : V) :
    0 ≤ gc9_pivotalMass ends F o g x y :=
  gc8_core_pairSum_nonneg ends _ F _ hF








noncomputable def gc9_assembledD (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (o g : V) : ℝ :=
  ∑ x : V, ∑ y : V, J s(x, y) * gc9_pivotalMass ends F o g x y













theorem gc9_assembledD_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (o g : V) (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m) :
    0 ≤ gc9_assembledD ends F J o g :=
  gc9_assembled_D_nonneg J (gc9_pivotalMass ends F o g) hJ
    (fun x y => gc9_concrete_delta_nonneg ends F hF o g x y)












noncomputable def gc9_pivotalMass_disconn (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o g : V)
    (x y : V) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)




noncomputable def gc9_assembledD_disconn (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (o g : V) : ℝ :=
  ∑ x : V, ∑ y : V, J s(x, y) * gc9_pivotalMass_disconn ends F o g x y








theorem gc9_assembledD_disconn_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ) (J : Sym2 V → ℝ)
    (o g : V) (hJ : ∀ e, 0 ≤ J e) (hF : ∀ m, 0 ≤ F m)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    
    (hdist : ∀ x y : V, o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
    (hsrcSet : ∀ x y : V, ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    0 ≤ gc9_assembledD_disconn ends F J o g := by
  refine Finset.sum_nonneg fun x _ => Finset.sum_nonneg fun y _ => ?_
  refine mul_nonneg (hJ _) ?_
  obtain ⟨hox, hoy, hog, hxy, hxg, hyg⟩ := hdist x y
  exact gc8_core_delta_nonneg ends F hox hoy hog hxy hxg hyg hnd hF (hsrcSet x y)















theorem gc9_assembled_D_nonneg_independent_of_u3 (J : Sym2 V → ℝ) (δ : V → V → ℝ) :
    (∀ e, 0 ≤ J e) → (∀ x y, 0 ≤ δ x y) → 0 ≤ ∑ x : V, ∑ y : V, J s(x, y) * δ x y :=
  fun hJ hδ => gc9_assembled_D_nonneg J δ hJ hδ














theorem gc9_assembled_D_nonneg_nonvacuous :
    0 ≤ gc9_assembledD (witEnds : Fin 2 → Sym2 (Fin 4)) (fun _ => 1) (fun _ => 1) (0 : Fin 4) 3 :=
  gc9_assembledD_nonneg witEnds (fun _ => 1) (fun _ => 1) 0 3
    (fun _ => by norm_num) (fun _ => by norm_num)

end StatMech.Walls
