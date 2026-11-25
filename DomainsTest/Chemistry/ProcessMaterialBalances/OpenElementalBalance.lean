/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import Domains.Chemistry.ProcessMaterialBalances.OpenElementalBalance
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.NormNum

/-! # Tests for open elemental balance -/

open Matrix MathlibExt.Chemistry.ProcessMaterialBalances.OpenElementalBalance

-- A nonzero reaction column cancels for every rate, irrespective of the time interval.
example (q : Fin 1 → ℝ) :
    !![(1 : ℝ), 1] *ᵥ (!![-1; 1] *ᵥ q) = 0 := by
  have hbalanced (r : Fin 1) :
      Chemistry.Stoichiometry.IsBalanced (!![1, 1] : Matrix (Fin 1) (Fin 2) ℝ)
        ((!![-1; 1] : Matrix (Fin 2) (Fin 1) ℝ).col r) := by
    rw [Subsingleton.elim r 0]
    funext b
    rw [Subsingleton.elim b 0]
    norm_num [Chemistry.Stoichiometry.IsBalanced, Matrix.mulVec, Matrix.col, dotProduct,
      Fin.sum_univ_two]
  exact (open_elemental_balance _ _ ∅ convex_empty 0 0 0 0 hbalanced (by simp)).2.1 q

-- Without balance the same row sees a nonzero source.
example : ((!![(1 : ℝ), 1]) *ᵥ ![-1, 2]) 0 = 1 := by
  norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
