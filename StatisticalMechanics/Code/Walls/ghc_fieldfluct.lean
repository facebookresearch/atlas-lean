/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/






















































import Mathlib
import Code.Sharpness.GHSFull

open scoped BigOperators
open Finset

set_option linter.unusedSectionVars false

namespace StatMech.Walls

open StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]






noncomputable def totalSpinM (s : ConfigSpace V) : ℝ := ∑ x, spin s x

@[simp] lemma totalSpinM_eq (s : ConfigSpace V) :
    totalSpinM s = totalSpin s := rfl













theorem ghc_field_fluctuation_hasDerivAt (β h : ℝ) (f : ConfigSpace V → ℝ) :
    HasDerivAt (fun h => isingExpectation G β h f)
      (β * (isingExpectation G β h (fun s => f s * totalSpinM s)
            - isingExpectation G β h f * isingExpectation G β h totalSpinM)) h :=
  hasDerivAt_expectation G β h f





theorem ghc_field_fluctuation_deriv (β h : ℝ) (f : ConfigSpace V → ℝ) :
    deriv (fun h => isingExpectation G β h f) h
      = β * (isingExpectation G β h (fun s => f s * totalSpinM s)
            - isingExpectation G β h f * isingExpectation G β h totalSpinM) :=
  (ghc_field_fluctuation_hasDerivAt G β h f).deriv




theorem ghc_field_fluctuation_differentiableAt (β h : ℝ) (f : ConfigSpace V → ℝ) :
    DifferentiableAt ℝ (fun h => isingExpectation G β h f) h :=
  (ghc_field_fluctuation_hasDerivAt G β h f).differentiableAt






theorem ghc_susceptibility_hasDerivAt (β h : ℝ) (o : V) :
    HasDerivAt (fun h => isingExpectation G β h (fun s => spin s o))
      (β * (isingExpectation G β h (fun s => spin s o * totalSpinM s)
            - isingExpectation G β h (fun s => spin s o)
                * isingExpectation G β h totalSpinM)) h :=
  ghc_field_fluctuation_hasDerivAt G β h (fun s => spin s o)



theorem ghc_susceptibility_deriv (β h : ℝ) (o : V) :
    deriv (fun h => isingExpectation G β h (fun s => spin s o)) h
      = β * (isingExpectation G β h (fun s => spin s o * totalSpinM s)
            - isingExpectation G β h (fun s => spin s o)
                * isingExpectation G β h totalSpinM) :=
  (ghc_susceptibility_hasDerivAt G β h o).deriv

end StatMech.Walls
