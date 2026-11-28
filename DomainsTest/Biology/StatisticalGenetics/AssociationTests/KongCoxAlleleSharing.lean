/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.AssociationTests.KongCoxAlleleSharing
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.NormNum

open WantedExt.Biology.StatisticalGenetics.KongCoxAlleleSharingWanted

-- The two log-affine terms have different signed slopes and both contribute to the score.
example : HasDerivAt (fun δ : ℝ => Real.log (1 + δ * 6) + Real.log (1 + δ * (-1))) 5 0 := by
  have h := hasDerivAt_sum_log_zero (![(2 : ℝ), 1]) (![3, -1])
  norm_num [Fin.sum_univ_two] at h ⊢
  exact h

-- An empty set of pedigrees gives the constant zero function and zero score.
example : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 0 := by
  simpa using (hasDerivAt_sum_log_zero (ι := Fin 0) (fun _ => 1) (fun _ => 1))

-- Independent of `likelihood_eq`: sum the two null observation contributions.
example : likelihood (fun _ : Fin 2 => 1 / 2) ![-1, 1] ![1 / 4, 3 / 4] 1 0 = 1 / 2 := by
  rw [likelihood_zero]
  norm_num [Fin.sum_univ_two]

-- The factorization's public API at a positive parameter, with a nonzero baseline.
example (hvar : 0 < nullVariance (fun _ : Fin 2 => 1 / 2) ![-1, 1]) :
    likelihood (fun _ : Fin 2 => 1 / 2) ![-1, 1] ![1 / 4, 3 / 4] 1 (1 / 2) =
      (1 / 2) * (1 + (1 / 2) *
        posteriorMeanScore (fun _ : Fin 2 => 1 / 2) ![-1, 1] ![1 / 4, 3 / 4]) := by
  have h := likelihood_eq (fun _ : Fin 2 => 1 / 2) ![-1, 1] ![1 / 4, 3 / 4]
    (by norm_num [Fin.sum_univ_two]) hvar (by norm_num [Fin.sum_univ_two]) 1 (1 / 2)
  rw [likelihood_zero] at h
  norm_num [Fin.sum_univ_two] at h
  exact h
