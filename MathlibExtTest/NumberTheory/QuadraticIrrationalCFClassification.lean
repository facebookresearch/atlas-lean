/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticIrrationalCFClassification

/-! # Tests for the parity criterion for symmetric continued fractions -/

open MetaMathlibExt

-- At the shortest admissible length, the block [2, 2] has odd denominator 5.
example : ∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
    HasPeriodicCF ((1 + √(d : ℝ)) / 2) b (fun _ => 2) 3 (2 * b - 1) := by
  apply (half_one_add_sqrt_hasPeriodicCF_exists_iff_parity 3 (by decide) _ (fun _ _ _ => by decide)
    (fun _ _ _ => rfl)).mpr
  decide

-- The block [1, 1] has even denominator 2 and both shorter continuants equal 1.
example : ∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
    HasPeriodicCF ((1 + √(d : ℝ)) / 2) b (fun _ => 1) 3 (2 * b - 1) := by
  apply (half_one_add_sqrt_hasPeriodicCF_exists_iff_parity 3 (by decide) _ (fun _ _ _ => by decide)
    (fun _ _ _ => rfl)).mpr
  decide

-- The block [4, 1, 4, 1, 4] has continuants 140, 29 and 6, so it is excluded.
example :
    let a (n : ℕ) := if n % 2 = 0 then 1 else 4
    ¬∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a 6 (2 * b - 1) := by
  intro a
  have hp (i : ℕ) (_ : 1 ≤ i) (_ : i < 6) : 0 < a i := by dsimp [a]; split <;> decide
  have hs (i : ℕ) (_ : 1 ≤ i) (hi : i < 6) : a i = a (6 - i) := by
    dsimp [a]
    split <;> split <;> omega
  rw [half_one_add_sqrt_hasPeriodicCF_exists_iff_parity 6 (by decide) a hp hs]
  decide
