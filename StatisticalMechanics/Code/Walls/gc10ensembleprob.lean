/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/





























































































import Mathlib
import Code.Sharpness.DeltaRewriteDichotomy
import Code.Walls.gc10deltasupport
import Code.Ising.CurrentWeight

open Finset BigOperators SimpleGraph
open scoped symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Ising
open StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent

variable {ι V : Type*} [DecidableEq ι] [Fintype ι] [DecidableEq V] [Fintype V]


















noncomputable def gc10_partitionFunction (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun _ => True)








noncomputable def gc10_allConnMass (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ) : ℝ :=
  drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m)






noncomputable def gc10_allConnProb (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ) : ℝ :=
  gc10_allConnMass ends o x y g F / gc10_partitionFunction ends o x y g F

















theorem gc10_pairSum_mono (ends : ι → Sym2 V) (A : Finset V) (F : Finset ι → ℝ)
    (P Q : Finset ι → Prop) (hF : ∀ m, 0 ≤ F m) (hPQ : ∀ m, P m → Q m) :
    drd_pairSum ends A F P ≤ drd_pairSum ends A F Q := by
  unfold drd_pairSum
  refine Finset.sum_le_sum (fun m _ => Finset.sum_le_sum (fun K _ => ?_))
  refine mul_le_mul_of_nonneg_left ?_ (hF m)
  by_cases hp : P m
  · simp [hp, hPQ m hp]
  · by_cases hq : Q m <;> simp [hp, hq]









theorem gc10_partitionFunction_nonneg (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ)
    (hF : ∀ m, 0 ≤ F m) :
    0 ≤ gc10_partitionFunction ends o x y g F :=
  (gc10_pairSum_is_sum_of_nonneg_terms ends _ F _ hF).2




theorem gc10_allConnMass_nonneg (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ)
    (hF : ∀ m, 0 ≤ F m) :
    0 ≤ gc10_allConnMass ends o x y g F :=
  (gc10_pairSum_is_sum_of_nonneg_terms ends _ F _ hF).2





















theorem gc10_allConnMass_le_partitionFunction (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ)
    (hF : ∀ m, 0 ≤ F m) :
    gc10_allConnMass ends o x y g F ≤ gc10_partitionFunction ends o x y g F :=
  gc10_pairSum_mono ends _ F (fun m => gc8_disconn ends o g m) (fun _ => True) hF (fun m _ => trivial)










theorem gc10_allConnProb_eq (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ) :
    gc10_allConnProb ends o x y g F
      = gc10_allConnMass ends o x y g F / gc10_partitionFunction ends o x y g F :=
  rfl




theorem gc10_allConnProb_nonneg (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ)
    (hF : ∀ m, 0 ≤ F m) :
    0 ≤ gc10_allConnProb ends o x y g F :=
  div_nonneg (gc10_allConnMass_nonneg ends o x y g F hF)
    (gc10_partitionFunction_nonneg ends o x y g F hF)





theorem gc10_allConnProb_le_one (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ)
    (hF : ∀ m, 0 ≤ F m) :
    gc10_allConnProb ends o x y g F ≤ 1 := by
  unfold gc10_allConnProb
  have hZ : 0 ≤ gc10_partitionFunction ends o x y g F :=
    gc10_partitionFunction_nonneg ends o x y g F hF
  rcases eq_or_lt_of_le hZ with hz | hz
  · simp [← hz]
  · rw [div_le_one hz]
    exact gc10_allConnMass_le_partitionFunction ends o x y g F hF











theorem gc10_allConnProb_mem_Icc (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ)
    (hF : ∀ m, 0 ≤ F m) :
    gc10_allConnProb ends o x y g F ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨gc10_allConnProb_nonneg ends o x y g F hF, gc10_allConnProb_le_one ends o x y g F hF⟩




















theorem gc10_allConnMass_eq_caseA_plus_caseB (ends : ι → Sym2 V) (F : Finset ι → ℝ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g}) :
    gc10_allConnMass ends o x y g F
      = drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
        + drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m) :=
  gc10_delta_eq_caseA_plus_caseB ends F hox hoy hog hxy hxg hyg hnd hsrcSet










theorem gc10_caseA_caseB_le_partitionFunction (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ)
    (hF : ∀ m, 0 ≤ F m) :
    drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseA ends o x y g m)
        ≤ gc10_partitionFunction ends o x y g F
      ∧ drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_caseB ends o x y g m)
        ≤ gc10_partitionFunction ends o x y g F :=
  ⟨gc10_pairSum_mono ends _ F (fun m => gc8_caseA ends o x y g m) (fun _ => True) hF
      (fun m _ => trivial),
   gc10_pairSum_mono ends _ F (fun m => gc8_caseB ends o x y g m) (fun _ => True) hF
      (fun m _ => trivial)⟩























theorem gc10_allConnProb_ferro (G : SimpleGraph V) [DecidableRel G.Adj] (β : ℝ) (J : Sym2 V → ℝ)
    (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e) (ends : ι → Sym2 V)
    (n₁ n₂ : Finset ι → Sharpness.Current V) (o x y g : V) :
    gc10_allConnMass ends o x y g (fun m => weight G β J (n₁ m) * weight G β J (n₂ m))
        ≤ gc10_partitionFunction ends o x y g (fun m => weight G β J (n₁ m) * weight G β J (n₂ m))
      ∧ gc10_allConnProb ends o x y g (fun m => weight G β J (n₁ m) * weight G β J (n₂ m))
          ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨gc10_allConnMass_le_partitionFunction ends o x y g _
      (fun m => gc10_ferro_mass_nonneg G β J hβ hJ (n₁ m) (n₂ m)),
   gc10_allConnProb_mem_Icc ends o x y g _
      (fun m => gc10_ferro_mass_nonneg G β J hβ hJ (n₁ m) (n₂ m))⟩


















theorem gc10_u3_nonpos_of_ensemble (ends : ι → Sym2 V) (o x y g : V) (F : Finset ι → ℝ)
    (hF : ∀ m, 0 ≤ F m) (u₃ : ℝ) (hid : u₃ = -2 * gc10_allConnMass ends o x y g F) :
    u₃ ≤ 0 := by
  rw [hid]
  have hN : 0 ≤ gc10_allConnMass ends o x y g F := gc10_allConnMass_nonneg ends o x y g F hF
  nlinarith [hN]













theorem gc10_allConnProb_mem_Icc_nonvacuous :
    gc10_allConnMass (witEnds) (0 : Fin 4) 1 2 3 (fun _ => (1 : ℝ))
        ≤ gc10_partitionFunction (witEnds) (0 : Fin 4) 1 2 3 (fun _ => (1 : ℝ))
      ∧ gc10_allConnProb (witEnds) (0 : Fin 4) 1 2 3 (fun _ => (1 : ℝ)) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨gc10_allConnMass_le_partitionFunction witEnds (0 : Fin 4) 1 2 3 (fun _ => 1)
      (fun _ => zero_le_one),
   gc10_allConnProb_mem_Icc witEnds (0 : Fin 4) 1 2 3 (fun _ => 1) (fun _ => zero_le_one)⟩

end StatMech.Walls
