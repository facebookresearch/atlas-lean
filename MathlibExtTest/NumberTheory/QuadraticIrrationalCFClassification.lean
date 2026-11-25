/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.QuadraticIrrationalCFClassification

/-! # Tests for the parity criterion and the classification for symmetric continued fractions -/

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

-- At length one every block occurs: the golden ratio is [1; 1, 1, …].
example (a : ℕ → ℕ) : ∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
    HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a 1 (2 * b - 1) :=
  (half_one_add_sqrt_hasPeriodicCF_exists_classification 1 a (fun _ _ _ => by omega)
    (fun _ _ _ => by omega)).1 odd_one

-- At length two the single digit must be odd: [b; 2, 2b - 1] never occurs.
example : ¬∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
    HasPeriodicCF ((1 + √(d : ℝ)) / 2) b (fun _ => 2) 2 (2 * b - 1) := by
  rw [(half_one_add_sqrt_hasPeriodicCF_exists_classification 2 _ (fun _ _ _ => by decide)
    (fun _ _ _ => rfl)).2 even_two two_pos]
  decide

-- The odd digit 3 occurs at length two.
example : ∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
    HasPeriodicCF ((1 + √(d : ℝ)) / 2) b (fun _ => 3) 2 (2 * b - 1) :=
  ((half_one_add_sqrt_hasPeriodicCF_exists_classification 2 _ (fun _ _ _ => by decide)
    (fun _ _ _ => rfl)).2 even_two two_pos).mpr (by decide)

-- At length four the block [1, 2, 1] has an even middle term, so it never occurs.
example :
    let a (n : ℕ) := if n = 2 then 2 else 1
    ¬∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a 4 (2 * b - 1) := by
  intro a
  have hp (i : ℕ) (_ : 1 ≤ i) (_ : i < 4) : 0 < a i := by dsimp [a]; split <;> decide
  have hs (i : ℕ) (_ : 1 ≤ i) (hi : i < 4) : a i = a (4 - i) := by
    dsimp [a]
    split <;> split <;> omega
  rw [(half_one_add_sqrt_hasPeriodicCF_exists_classification 4 a hp hs).2 (by decide)
    (by decide)]
  decide

-- At odd length five the block [2, 1, 1, 2] occurs.
example :
    let a (n : ℕ) := if n = 1 ∨ n = 4 then 2 else 1
    ∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a 5 (2 * b - 1) := by
  intro a
  have hp (i : ℕ) (_ : 1 ≤ i) (_ : i < 5) : 0 < a i := by dsimp [a]; split <;> decide
  have hs (i : ℕ) (_ : 1 ≤ i) (hi : i < 5) : a i = a (5 - i) := by
    dsimp [a]
    split <;> split <;> omega
  exact (half_one_add_sqrt_hasPeriodicCF_exists_classification 5 a hp hs).1 (by decide)
