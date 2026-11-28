/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.AssociationTests.ConditionalLogisticMatchedSets
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.NormNum

/-!
# Tests for matched-set conditional case probabilities
-/

open WantedExt.Biology.StatisticalGenetics.ConditionalLogisticMatchedSetsWanted

private def pairExposures (i : Fin 2) (_ : Fin 1) : ℝ := i.val

-- The exposures 0 and 1 are both shifted by 3, with a nonzero coefficient.
example (α : ℝ) :
    conditionalCaseProb (M := 1) α (fun _ => Real.log 2) (fun i => pairExposures i + fun _ => 3) 0 =
      conditionalCaseProb (M := 1) α (fun _ => Real.log 2) pairExposures 0 :=
  conditionalCaseProb_add_const α (fun _ => Real.log 2) pairExposures (fun _ => 3) 0

-- At coefficient log 2, the two unshifted weights are 1 and 2, regardless of the intercept.
example (α : ℝ) :
    conditionalCaseProb (M := 1) α (fun _ => Real.log 2) pairExposures 0 = 1 / 3 := by
  rw [conditionalCaseProb_eq, Fin.sum_univ_two]
  simp [dotProduct, pairExposures, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num
