/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Analysis.Convex.LinearProgrammingCertificate
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum.Ineq

/-!
# Clients of the LP certificate

A feasible primal/dual pair with equal objectives is optimal for both.
The examples are tight pairs: a 1-dim pair with equal value `10` and a
2-var pair with equal value `6`.
-/

namespace LinearProgrammingCertificateTest

open MathlibExt.Analysis.Convex.LPCertificate
open scoped Matrix

/-- 1-dim tight pair: `x = 5, y = 2` have equal value and are optimal. -/
example : (∀ x' : Fin 1 → ℝ, (∀ i, 0 ≤ x' i) →
    (∀ j, (1 : Matrix (Fin 1) (Fin 1) ℝ).mulVec x' j ≤ ![5] j) →
    ![2] ⬝ᵥ x' ≤ ![2] ⬝ᵥ ![5]) ∧
    (∀ y' : Fin 1 → ℝ, (∀ j, 0 ≤ y' j) →
    (∀ i, ![2] i ≤ ((1 : Matrix (Fin 1) (Fin 1) ℝ)ᵀ.mulVec y') i) →
    ![5] ⬝ᵥ ![2] ≤ ![5] ⬝ᵥ y') :=
  feasible_pair_equal_objectives_optimal
    (1 : Matrix (Fin 1) (Fin 1) ℝ) ![5] ![2]
    (x := ![5]) (by norm_num [Fin.forall_fin_one])
    (by norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct])
    (y := ![2]) (by norm_num [Fin.forall_fin_one])
    (by norm_num [Fin.forall_fin_one, Matrix.mulVec, dotProduct, Matrix.transpose_apply])
    (by norm_num [dotProduct])

/-- 2-var tight pair: `x = (3, 0), y = 2` have equal value `6` and are optimal. -/
example : (∀ x' : Fin 2 → ℝ, (∀ i, 0 ≤ x' i) →
    (∀ j, (Matrix.of ![![1, 1]] : Matrix (Fin 1) (Fin 2) ℝ).mulVec x' j ≤ ![3] j) →
    ![2, 1] ⬝ᵥ x' ≤ ![2, 1] ⬝ᵥ ![3, 0]) ∧
    (∀ y' : Fin 1 → ℝ, (∀ j, 0 ≤ y' j) →
    (∀ i, ![2, 1] i ≤ ((Matrix.of ![![1, 1]] : Matrix (Fin 1) (Fin 2) ℝ)ᵀ.mulVec y') i) →
    ![3] ⬝ᵥ ![2] ≤ ![3] ⬝ᵥ y') :=
  feasible_pair_equal_objectives_optimal
    (Matrix.of ![![1, 1]] : Matrix (Fin 1) (Fin 2) ℝ) ![3] ![2, 1]
    (x := ![3, 0]) (by norm_num [Fin.forall_fin_two])
    (by norm_num [Fin.forall_fin_one, Fin.forall_fin_two, Matrix.mulVec, dotProduct])
    (y := ![2]) (by norm_num [Fin.forall_fin_one])
    (by norm_num [Fin.forall_fin_two, Fin.forall_fin_one, Matrix.mulVec, dotProduct,
      Matrix.transpose_apply])
    (by norm_num [dotProduct, Fin.sum_univ_two])

end LinearProgrammingCertificateTest
