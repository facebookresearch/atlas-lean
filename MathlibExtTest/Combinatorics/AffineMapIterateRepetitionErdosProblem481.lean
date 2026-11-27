/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import MathlibExt.Combinatorics.AffineMapIterateRepetitionErdosProblem481

open MathlibExt.Combinatorics.AffineMapIterateRepetitionErdosProblem481Wanted

-- Two distinct translations first collide at the second expansion.
example :
    let T := affineExpand (fun _ : Fin 2 ↦ 1) (fun i ↦ i.val + 1)
    (T [1]).Nodup ∧ T^[2] [1] = [3, 4, 4, 5] ∧ ¬ (T^[2] [1]).Nodup := by
  decide

-- At reciprocal sum one the even and odd blocks can still have distinct entries.
example :
    let T := affineExpand (fun _ : Fin 2 ↦ 2) (fun i ↦ i.val)
    T^[2] [1] = [4, 6, 5, 7] ∧ (T^[2] [1]).Nodup := by
  decide

-- Slopes one and two satisfy the strict bound for any choice of translations.
example (b : Fin 2 → ℕ) :
    ∃ k : ℕ, ¬ ((affineExpand (fun i : Fin 2 ↦ i.val + 1) b)^[k] [1]).Nodup := by
  apply affineIterateHasRepetition_holds
  · intro i
    exact Nat.succ_pos _
  · norm_num [Fin.sum_univ_two]
