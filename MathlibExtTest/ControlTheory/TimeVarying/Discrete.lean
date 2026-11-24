/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.ControlTheory.TimeVarying.Discrete
import Mathlib.LinearAlgebra.Matrix.Notation

open Matrix

namespace ControlTheory

-- Ordered products of a constant family recover ordinary powers.
example (M : Matrix (Fin 2) (Fin 2) ℤ) :
    orderedProd (fun _ => M) 3 0 = M ^ 3 :=
  orderedProd_const M 3

-- A two-step ordered product puts the later factor on the left.
example (A : ℕ → Matrix (Fin 2) (Fin 2) ℤ) :
    orderedProd A 2 0 = A 1 * A 0 := by
  have h1 : orderedProd A 1 0 = A 0 := by simp [orderedProd]
  rw [orderedProd_succ_of_le A (Nat.zero_le 1), h1]

-- A reversed interval is the empty product.
example (A : ℕ → Matrix (Fin 2) (Fin 2) ℤ) :
    orderedProd A 1 2 = 1 :=
  orderedProd_of_le A (Nat.le_succ 1)

-- Noncommuting witness: the two orders differ.
example : (!![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) ℤ) * !![1, 0; 1, 1] ≠
    !![1, 0; 1, 1] * !![1, 1; 0, 1] := by
  decide

-- The trajectory formula at two steps, with noncommuting factors:
-- the recursive trajectory and the ordered-product formula both give
-- `![4, 3]`, and the formula expands with the later factor on the left.
example :
    let A : ℕ → Matrix (Fin 2) (Fin 2) ℤ := fun k => if k = 0 then !![1, 1; 0, 1] else !![1, 0; 1, 1]
    let B : ℕ → Matrix (Fin 2) (Fin 2) ℤ := fun _ => 1
    let u : ℕ → Fin 2 → ℤ := fun k => if k = 0 then ![1, 0] else ![0, 1]
    tvTraj A B u ![5, -2] 2 = ![4, 3] ∧
      tvTraj A B u ![5, -2] 2 =
        (A 1 * A 0) *ᵥ ![5, -2] + A 1 *ᵥ (B 0 *ᵥ u 0) + B 1 *ᵥ u 1 := by
  decide

-- The ordered product is available over the natural-number semiring.
example (A : ℕ → Matrix (Fin 2) (Fin 2) ℕ) :
    orderedProd A 2 0 = A 1 * A 0 := by
  have h1 : orderedProd A 1 0 = A 0 := by simp [orderedProd]
  rw [orderedProd_succ_of_le A (Nat.zero_le 1), h1]

example (A : ℕ → Matrix (Fin 2) (Fin 2) ℕ) :
    orderedProd A 1 2 = 1 :=
  orderedProd_of_le A (Nat.le_succ 1)

end ControlTheory
