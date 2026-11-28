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

-- At length two there is only one prescribed digit, and either parity is realizable.
example (m : ℕ) (hm : 0 < m) :
    ∃ d b : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) b (fun _ => m) 2 (2 * b) := by
  apply (sqrt_hasPeriodicCF_exists_iff_of_even 2 (by decide) (by decide) _
    (fun _ _ _ => hm) (fun _ _ _ => rfl)).mpr
  simpa [convergentDen_one] using (Nat.even_or_odd m).symm

-- The block [1, 1, 1] has odd midpoint and odd final continuant (3).
example : ∃ d b : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) b (fun _ => 1) 4 (2 * b) := by
  apply (sqrt_hasPeriodicCF_exists_iff_of_even 4 (by decide) (by decide) _
    (fun _ _ _ => by decide) (fun _ _ _ => rfl)).mpr
  decide

-- The block [2, 2, 2] has even midpoint and even final continuant (12).
example : ∃ d b : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) b (fun _ => 2) 4 (2 * b) := by
  apply (sqrt_hasPeriodicCF_exists_iff_of_even 4 (by decide) (by decide) _
    (fun _ _ _ => by decide) (fun _ _ _ => rfl)).mpr
  decide

-- The block [2, 1, 2] has odd midpoint but even final continuant (8).
example :
    let a (i : ℕ) := if i = 2 then 1 else 2
    ¬∃ d b : ℕ, ¬IsSquare d ∧ HasPeriodicCF √(d : ℝ) b a 4 (2 * b) := by
  intro a
  have hp (i : ℕ) (_ : 1 ≤ i) (_ : i < 4) : 0 < a i := by dsimp [a]; split <;> decide
  have hs (i : ℕ) (_ : 1 ≤ i) (_ : i < 4) : a i = a (4 - i) := by
    have he : i = 2 ↔ 4 - i = 2 := by omega
    simp [a, ← he]
  rw [sqrt_hasPeriodicCF_exists_iff_of_even 4 (by decide) (by decide) a hp hs]
  decide

private noncomputable def obstructionCount (l : ℕ) : ℕ :=
  Set.ncard {v : Fin (l / 2) → ZMod 2 | ¬∃ a : ℕ → ℕ,
    (∀ i, 1 ≤ i → i < l → 0 < a i) ∧ (∀ i, 1 ≤ i → i < l → a i = a (l - i)) ∧
    (∀ j : Fin (l / 2), (a ((j : ℕ) + 1) : ZMod 2) = v j) ∧
    ∃ d b : ℕ, d % 4 = 1 ∧ ¬IsSquare d ∧
      HasPeriodicCF ((1 + √(d : ℝ)) / 2) b a l (2 * b - 1)}

-- At length two the symmetric block consists of a single digit.
example : obstructionCount 2 = 1 :=
  half_one_add_sqrt_periodicCF_obstruction_count_of_even 2 (by decide) (by decide)

-- At lengths four and six there are respectively one and two free coordinates.
example : obstructionCount 4 = 2 :=
  half_one_add_sqrt_periodicCF_obstruction_count_of_even 4 (by decide) (by decide)

example : obstructionCount 6 = 4 :=
  half_one_add_sqrt_periodicCF_obstruction_count_of_even 6 (by decide) (by decide)
