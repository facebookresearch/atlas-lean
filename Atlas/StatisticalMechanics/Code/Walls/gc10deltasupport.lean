/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































































import Mathlib
import Code.Walls.gc8crossingallconn
import Code.Walls.gc9switching
import Code.Ising.CurrentWeight

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Ising
open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V] [Fintype V]













theorem gc10_pairSum_term_nonneg (w : ℝ) (hw : 0 ≤ w) (P : Prop) [Decidable P] :
    0 ≤ w * (if P then (1 : ℝ) else 0) := by
  refine mul_nonneg hw ?_
  split <;> norm_num









theorem gc10_pairSum_is_sum_of_nonneg_terms (ends : ι → Sym2 V) (A : Finset V) (F : Finset ι → ℝ)
    (P : Finset ι → Prop) (hF : ∀ m, 0 ≤ F m) :
    drd_pairSum ends A F P
        = ∑ m ∈ (Finset.univ.powerset.filter (fun m => RandomCurrent.sources ends m = A)),
            (∑ _K ∈ m.powerset.filter (fun K => RandomCurrent.sources ends K = A),
                F m * (if P m then (1 : ℝ) else 0))
      ∧ 0 ≤ drd_pairSum ends A F P := by
  refine ⟨rfl, ?_⟩
  unfold drd_pairSum
  refine Finset.sum_nonneg (fun m _ => Finset.sum_nonneg (fun K _ => ?_))
  exact gc10_pairSum_term_nonneg (F m) (hF m) (P m)




theorem gc10_caseA_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V)
    (hF : ∀ m, 0 ≤ F m) :
    0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) :=
  (gc10_pairSum_is_sum_of_nonneg_terms ends _ F _ hF).2




theorem gc10_caseB_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ) (o x y g : V)
    (hF : ∀ m, 0 ≤ F m) :
    0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) :=
  (gc10_pairSum_is_sum_of_nonneg_terms ends _ F _ hF).2
















theorem gc10_caseB_eq_swap (ends : ι → Sym2 V) (o x y g : V) (m : Finset ι) :
    gc8_caseB ends o x y g m = gc8_caseA ends o y x g m :=
  gc8_caseB_eq_swap ends o x y g m










theorem gc10_delta_eq_caseA_plus_caseB (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)
      = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
        + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) :=
  gc8_delta_eq_caseA_plus_caseB ends F hox hoy hog hxy hxg hyg hnd hsrcSet































theorem gc10_delta_support (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (hF : ∀ m, 0 ≤ F m)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    
    (drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)
        = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
          + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m))
    
    ∧ (∀ m : Finset ι, gc8_caseB ends o x y g m = gc8_caseA ends o y x g m)
    
    ∧ (0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m))
    ∧ (0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m))
    
    ∧ (0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)) := by
  have hdecomp :
      drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)
        = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
          + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) :=
    gc10_delta_eq_caseA_plus_caseB ends F hox hoy hog hxy hxg hyg hnd hsrcSet
  have hA : 0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m) :=
    gc10_caseA_nonneg ends F o x y g hF
  have hB : 0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) :=
    gc10_caseB_nonneg ends F o x y g hF
  refine ⟨hdecomp, fun m => gc10_caseB_eq_swap ends o x y g m, hA, hB, ?_⟩
  
  rw [hdecomp]; exact add_nonneg hA hB




theorem gc10_delta_nonneg (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (hF : ∀ m, 0 ≤ F m)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) :=
  (gc10_delta_support ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet).2.2.2.2











theorem gc10_ferro_mass_nonneg (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (n₁ n₂ : Sharpness.Current V) :
    0 ≤ weight G β J n₁ * weight G β J n₂ :=
  mul_nonneg (acw_weight_nonneg G β J hβ hJ n₁) (acw_weight_nonneg G β J hβ hJ n₂)












theorem gc10_delta_support_ferro (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (ends : ι → Sym2 V)
    (n₁ n₂ : Finset ι → Sharpness.Current V)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V)
          (fun m => weight G β J (n₁ m) * weight G β J (n₂ m))
          (fun m => gc8_disconn ends o g m) :=
  gc10_delta_nonneg ends _ hox hoy hog hxy hxg hyg hnd
    (fun m => gc10_ferro_mass_nonneg G β J hβ hJ (n₁ m) (n₂ m)) hsrcSet

















theorem gc10_delta_support_uses_no_ursell (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    (o x y g : V)
    (hdist : o ≠ x ∧ o ≠ y ∧ o ≠ g ∧ x ≠ y ∧ x ≠ g ∧ y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hmass : ∀ m, 0 ≤ F m)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    0 ≤ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) := by
  obtain ⟨hox, hoy, hog, hxy, hxg, hyg⟩ := hdist
  exact gc10_delta_nonneg ends F hox hoy hog hxy hxg hyg hnd hmass hsrcSet












theorem gc10_delta_support_nonvacuous :
    0 ≤ drd_pairSum (witEnds) ({0, 1, 2, 3} : Finset (Fin 4)) (fun _ => (1 : ℝ))
        (fun m => gc8_disconn witEnds (0 : Fin 4) 3 m) :=
  (gc10_pairSum_is_sum_of_nonneg_terms witEnds _ (fun _ => 1) _ (fun _ => zero_le_one)).2

end StatMech.Walls
