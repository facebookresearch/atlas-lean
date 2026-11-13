/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
































































import Mathlib
import Code.Walls.gc8core

open Finset BigOperators SimpleGraph Set
open scoped symmDiff

namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness
open StatMech.Sharpness.RandomCurrent

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ι : Type*} [DecidableEq ι] [Fintype ι]













theorem gc9_J_summand_nonneg
    (ends : ι → Sym2 V) (F : Finset ι → ℝ) {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g) (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hnd : ∀ i, ¬ (ends i).IsDiag) (hF : ∀ m, 0 ≤ F m)
    (hsrcSet : ∀ m : Finset ι, (¬ connK ends m o g) → sources ends m = {o, x, y, g})
    (Jxy : ℝ) (hJ : 0 ≤ Jxy) :
    0 ≤ Jxy * drd_pairSum ends ({o, x, y, g} : Finset V) F (fun m => gc8_disconn ends o g m) :=
  mul_nonneg hJ
    (gc8_core_delta_nonneg ends F hox hoy hog hxy hxg hyg hnd hF hsrcSet)





theorem gc9_J_summand_nonneg_of_delta (Jxy δxy : ℝ) (hJ : 0 ≤ Jxy) (hδ : 0 ≤ δxy) :
    0 ≤ Jxy * δxy :=
  mul_nonneg hJ hδ







theorem gc9_J_sum_nonneg {E : Type*} (s : Finset E) (J : E → ℝ) (δ : E → ℝ)
    (hJ : ∀ e ∈ s, 0 ≤ J e) (hδ : ∀ e ∈ s, 0 ≤ δ e) :
    0 ≤ ∑ e ∈ s, J e * δ e :=
  Finset.sum_nonneg (fun e he => gc9_J_summand_nonneg_of_delta (J e) (δ e) (hJ e he) (hδ e he))





theorem gc9_J_sum_scaled_nonneg {E : Type*} (s : Finset E) (J : E → ℝ) (δ : E → ℝ)
    (Z : ℝ) (hZ : 0 < Z) (hJ : ∀ e ∈ s, 0 ≤ J e) (hδ : ∀ e ∈ s, 0 ≤ δ e) :
    0 ≤ (1 / Z ^ 2) * ∑ e ∈ s, J e * δ e := by
  apply mul_nonneg
  · positivity
  · exact gc9_J_sum_nonneg s J δ hJ hδ












theorem gc9_J_deriv_eq20_nonneg {E : Type*} (s : Finset E)
    (J : E → ℝ) (Z : ℝ) (hZ : 0 < Z)
    (ends : E → ι → Sym2 V) (F : E → Finset ι → ℝ)
    (o : V) (xe ye : E → V) (g : V)
    (hox : ∀ e, o ≠ xe e) (hoy : ∀ e, o ≠ ye e) (hog : o ≠ g)
    (hxy : ∀ e, xe e ≠ ye e) (hxg : ∀ e, xe e ≠ g) (hyg : ∀ e, ye e ≠ g)
    (hnd : ∀ e i, ¬ (ends e i).IsDiag) (hF : ∀ e m, 0 ≤ F e m)
    (hsrcSet : ∀ e (m : Finset ι), (¬ connK (ends e) m o g) →
      sources (ends e) m = {o, xe e, ye e, g})
    (hJ : ∀ e ∈ s, 0 ≤ J e) :
    0 ≤ (1 / Z ^ 2) *
      ∑ e ∈ s, J e *
        drd_pairSum (ends e) ({o, xe e, ye e, g} : Finset V) (F e)
          (fun m => gc8_disconn (ends e) o g m) := by
  apply mul_nonneg
  · positivity
  · refine Finset.sum_nonneg (fun e he => ?_)
    exact gc9_J_summand_nonneg (ends e) (F e) (hox e) (hoy e) hog (hxy e) (hxg e) (hyg e)
      (hnd e) (hF e) (hsrcSet e) (J e) (hJ e he)

end StatMech.Walls
