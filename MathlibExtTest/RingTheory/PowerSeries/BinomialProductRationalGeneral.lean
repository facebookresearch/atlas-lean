/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.RingTheory.PowerSeries.BinomialProductRationalGeneral
import Mathlib.Tactic.NormNum

namespace MetaMathlibExt.BinomialProductRationalGeneralTest

open PowerSeries

-- The improper input X³/(1-X) contributes three extra copies of the second denominator.
example (A B : PowerSeries ℚ)
    (hA : A * (1 - X) = X ^ 3) (hB : B * (1 - C 2 * X) = 1) :
    ∃ T : Polynomial ℚ, T.degree < 4 ∧
      binomialProduct A B * ((1 - C 2 * X) ^ 3 * (1 - C 3 * X)) = (T : PowerSeries ℚ) := by
  have h := binomialProduct_rational_general 1 1 (fun _ ↦ (1 : ℚ)) (fun _ ↦ 2)
      (by intros; decide) (by intros; decide) (Polynomial.X ^ 3) 1 A B
      (by simpa using hA) (by simpa using hB)
  rw [Polynomial.natDegree_X_pow] at h
  simpa [-map_add, show (1 : ℚ) + 2 = 3 by norm_num] using h

-- With both lists empty, the binomial product of polynomials still has a bounded numerator.
example (R S : Polynomial ℚ) :
    ∃ T : Polynomial ℚ, T.degree < ((R.natDegree + 1) * (S.natDegree + 1) : ℕ) ∧
      binomialProduct (R : PowerSeries ℚ) S = (T : PowerSeries ℚ) := by
  simpa using binomialProduct_rational_general 0 0 Fin.elim0 Fin.elim0
    (fun i ↦ i.elim0) (fun j ↦ j.elim0) R S R S (by simp) (by simp)

end MetaMathlibExt.BinomialProductRationalGeneralTest
