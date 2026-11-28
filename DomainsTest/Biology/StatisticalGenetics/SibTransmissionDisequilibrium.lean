/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Biology.StatisticalGenetics.SibTransmissionDisequilibrium

open MathlibExt.Probability.Causality (randExp)
open WantedExt.Biology.StatisticalGenetics.SibTransmissionDisequilibriumWanted

-- The affected set is deterministic at both endpoints.
example {t : ℕ} (ht : 2 ≤ t) (x : Fin t → ℝ) :
    randExp 0 (fun S => affectedAlleleCount x S ^ 2) = 0 := by
  simpa using randExp_sq_sub_mean (a := 0) ht (Nat.zero_le t) x

example {t : ℕ} (ht : 2 ≤ t) (x : Fin t → ℝ) :
    randExp t (fun S => (affectedAlleleCount x S - ∑ j, x j) ^ 2) = 0 := by
  have ht0 : (t : ℝ) ≠ 0 := by exact_mod_cast (show t ≠ 0 by omega)
  simpa [mul_comm (t : ℝ), ht0] using randExp_sq_sub_mean ht (le_refl t) x

-- When one of two sibs is affected and their counts are 0 and 2, the mean and variance are 1.
example : randExp 1 (fun S => (affectedAlleleCount (![0, 2] : Fin 2 → ℝ) S - 1) ^ 2) = 1 := by
  have h := randExp_sq_sub_mean (t := 2) (a := 1) (by decide) (by decide)
    (![0, 2] : Fin 2 → ℝ)
  norm_num [Fin.sum_univ_two] at h
  exact h
