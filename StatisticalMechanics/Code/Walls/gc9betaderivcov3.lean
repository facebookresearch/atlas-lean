/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

































































































import Mathlib
import Code.Ising.AizenmanBarsky
import Code.Walls.ghc_fieldfluct

open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]















theorem gc9_beta_deriv_cov3 (β h : ℝ) (o : V) :
    deriv (fun β => isingExpectation G β h (fun s => spin s o)) β
      = bondEnergySusceptibility G β h o + h * susceptibility G β h o :=
  deriv_magnetization_beta_eq G β h o





theorem gc9_beta_deriv_hasDerivAt (β h : ℝ) (o : V) :
    HasDerivAt (fun β => isingExpectation G β h (fun s => spin s o))
      (bondEnergySusceptibility G β h o + h * susceptibility G β h o) β := by
  have hd := hasDerivAt_expectation_beta G β h (fun s => spin s o)
  rw [expectation_negHam_cov_expand] at hd
  
  have hbond : (∑ e ∈ G.edgeFinset,
        (isingExpectation G β h (fun s => spin s o * bond s e)
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => bond s e)))
      = bondEnergySusceptibility G β h o := by
    unfold bondEnergySusceptibility
    apply Finset.sum_congr rfl
    intro e _
    induction e with
    | h x y => rw [cov3sym_mk]; rfl
  have hfield : (∑ x,
        (isingExpectation G β h (fun s => spin s o * spin s x)
          - isingExpectation G β h (fun s => spin s o)
              * isingExpectation G β h (fun s => spin s x)))
      = susceptibility G β h o := by
    unfold susceptibility cov2; rfl
  rw [hbond, hfield] at hd
  exact hd











theorem gc9_beta_deriv_book_form (β h : ℝ) (o : V) :
    deriv (fun β => isingExpectation G β h (fun s => spin s o)) β
      = (∑ e ∈ G.edgeFinset,
          (isingExpectation G β h (fun s => spin s o * bond s e)
            - isingExpectation G β h (fun s => spin s o)
                * isingExpectation G β h (fun s => bond s e)))
        + h * ∑ x,
          (isingExpectation G β h (fun s => spin s o * spin s x)
            - isingExpectation G β h (fun s => spin s o)
                * isingExpectation G β h (fun s => spin s x)) := by
  rw [(hasDerivAt_expectation_beta G β h (fun s => spin s o)).deriv]
  exact expectation_negHam_cov_expand G β h (fun s => spin s o)









theorem gc9_field_term_eq_fieldFluct (β h : ℝ) (hβ : β ≠ 0) (o : V) :
    h * susceptibility G β h o
      = (h / β) * deriv (fun h => isingExpectation G β h (fun s => spin s o)) h := by
  rw [ghc_field_fluctuation_deriv]
  
  have hsusc : susceptibility G β h o
      = isingExpectation G β h (fun s => spin s o * totalSpinM s)
          - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpinM := by
    
    
    have hM : (totalSpinM : ConfigSpace V → ℝ) = totalSpin := rfl
    rw [hM, expectation_mul_totalSpin, expectation_totalSpin, Finset.mul_sum]
    unfold susceptibility cov2
    rw [Finset.sum_sub_distrib]
  rw [hsusc]
  field_simp






theorem gc9_beta_deriv_nonvacuous (β h : ℝ) :
    deriv (fun β => isingExpectation (⊤ : SimpleGraph (Fin 2)) β h (fun s => spin s 0)) β
      = bondEnergySusceptibility (⊤ : SimpleGraph (Fin 2)) β h 0
        + h * susceptibility (⊤ : SimpleGraph (Fin 2)) β h 0 :=
  gc9_beta_deriv_cov3 (⊤ : SimpleGraph (Fin 2)) β h 0

end StatMech.Walls
