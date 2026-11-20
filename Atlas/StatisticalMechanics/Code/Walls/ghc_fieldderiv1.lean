/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
























































import Mathlib
import Code.Ising.AizenmanBarsky

open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000

namespace StatMech

namespace Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

















theorem ghc_hasDerivAt_magnetization_field (β h : ℝ) (o : V) :
    HasDerivAt (fun h => isingExpectation G β h (fun s => spin s o))
      (β * (isingExpectation G β h (fun s => spin s o * totalSpin s)
            - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpin))
      h :=
  hasDerivAt_magnetization G β h o






theorem ghc_susceptibility_eq_sum_cov2 (β h : ℝ) (o : V) :
    susceptibility G β h o = ∑ x, cov2 G β h o x := rfl



theorem ghc_cov_summand_eq_cov2 (β h : ℝ) (o x : V) :
    isingExpectation G β h (fun s => spin s o * spin s x)
        - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h (fun s => spin s x)
      = cov2 G β h o x := rfl











theorem ghc_field_deriv1 (β h : ℝ) (o : V) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) h
      = β * susceptibility G β h o := by
  rw [deriv_magnetization_eq_sum_cov]
  rfl





theorem ghc_field_deriv1_sum (β h : ℝ) (o : V) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) h
      = β * ∑ x, cov2 G β h o x := by
  rw [ghc_field_deriv1, ghc_susceptibility_eq_sum_cov2]










theorem ghc_field_deriv1_hasDerivAt (β h : ℝ) (o : V) :
    HasDerivAt (fun h => isingExpectation G β h (fun s => spin s o))
      (β * susceptibility G β h o) h := by
  have hd := ghc_hasDerivAt_magnetization_field G β h o
  have hval : β * (isingExpectation G β h (fun s => spin s o * totalSpin s)
            - isingExpectation G β h (fun s => spin s o) * isingExpectation G β h totalSpin)
      = β * susceptibility G β h o := by
    rw [ghc_susceptibility_eq_sum_cov2, expectation_mul_totalSpin, expectation_totalSpin,
      Finset.mul_sum]
    congr 1
    rw [← Finset.sum_sub_distrib]
    rfl
  rwa [hval] at hd








theorem ghc_field_deriv1_nonneg (β h : ℝ) (hβ : 0 ≤ β) (hh : 0 ≤ h) (o : V) :
    0 ≤ deriv (fun h => isingExpectation G β h (fun s => spin s o)) h :=
  deriv_magnetization_nonneg G β h hβ hh o

end Walls

end StatMech
