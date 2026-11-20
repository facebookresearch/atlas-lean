/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






























































import Mathlib
import Code.Ising.GKS
import Code.Sharpness.CurrentRep
import Code.Ising.CorrelationRatio
import Code.Sharpness.FieldGhostDict

open Finset BigOperators SimpleGraph Set Classical
open scoped symmDiff

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option maxHeartbeats 800000

namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness StatMech.Sharpness.FieldGhostDict

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]














theorem gc6_mu_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) :
    0 ≤ isingExpectation G β h (spinProd A) :=
  gks_first G β h hβ hh A













theorem gc6_ghostCoupling_nonneg (β h : ℝ) (hh : 0 ≤ h) (e : Sym2 (Option V)) :
    0 ≤ ghostCoupling h β (fun _ => 1) e := by
  induction e with
  | h a b =>
    rcases a with _ | x <;> rcases b with _ | y <;>
      simp only [ghostCoupling, Sym2.lift_mk] <;> first | exact hh | norm_num






theorem gc6_Z_B_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) :
    0 ≤ currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (A.map someEmb) :=
  acr_currentSum_nonneg (withGhost G) β (ghostCoupling h β (fun _ => 1)) hβ
    (gc6_ghostCoupling_nonneg (V := V) β h hh) (A.map someEmb)






theorem gc6_Z0_pos (β h : ℝ) :
    0 < currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  acr_currentSum_empty_pos (withGhost G) β (ghostCoupling h β (fun _ => 1))











theorem gc6_mu_eq_ratio (β h : ℝ) (A : Finset V) (hA : Even A.card) :
    isingExpectation G β h (spinProd A)
      = currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) (A.map someEmb)
          / currentSum (withGhost G) β (ghostCoupling h β (fun _ => 1)) ∅ :=
  fgd_isingExpectation_eq_currentSum_ratio G β h A hA







theorem gc6_mu_nonneg_of_ratio (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) (hA : Even A.card) :
    0 ≤ isingExpectation G β h (spinProd A) := by
  rw [gc6_mu_eq_ratio G β h A hA]
  exact div_nonneg (gc6_Z_B_nonneg G β h hβ hh A) (gc6_Z0_pos G β h).le













theorem gc6_familyRealise_mu_clause (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (A : Finset V) :
    ∃ μ : ℝ, 0 ≤ μ ∧ μ = isingExpectation G β h (spinProd A) :=
  ⟨isingExpectation G β h (spinProd A), gc6_mu_nonneg G β h hβ hh A, rfl⟩









theorem gc6_mu_nonneg_nonvacuous :
    0 ≤ isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3))) :=
  gc6_mu_nonneg (⊤ : SimpleGraph (Fin 3)) 1 1 (by norm_num) (by norm_num) ({0, 1} : Finset (Fin 3))




theorem gc6_mu_eq_ratio_nonvacuous :
    isingExpectation (⊤ : SimpleGraph (Fin 3)) 1 1 (spinProd ({0, 1} : Finset (Fin 3)))
      = currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1))
            (({0, 1} : Finset (Fin 3)).map someEmb)
          / currentSum (withGhost (⊤ : SimpleGraph (Fin 3))) 1 (ghostCoupling 1 1 (fun _ => 1)) ∅ :=
  gc6_mu_eq_ratio (⊤ : SimpleGraph (Fin 3)) 1 1 ({0, 1} : Finset (Fin 3)) (by decide)

end StatMech.Walls
