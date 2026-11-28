/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.DiagonalCongruenceSolvability

/-!
# Tests for solvability of diagonal congruences
-/

open MetaMathlibExt

-- Both the cardinality of the index set and the prime are at their smallest allowed values.
example : ∃ x : Fin 1 → ℤ, ∑ i, (-3 : ℤ) * x i ^ 1 ≡ -1 [ZMOD 2] := by
  let _ : Fact (Nat.Prime 2) := ⟨by decide⟩
  exact diagonal_congruence_solvable_of_card_eq_exponent (p := 2) (k := 1)
    (hk := by decide) (a := fun _ => -3) (ha := fun _ => by decide) (c := -1)

-- Modulo 7, each scaled square set is {0, 3, 5, 6}, so neither summand alone can give 4.
example : ∃ x : Fin 2 → ℤ,
    ∑ i, (if i = 0 then (-2 : ℤ) else 3) * x i ^ 2 ≡ -3 [ZMOD 7] := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine diagonal_congruence_solvable_of_card_eq_exponent (p := 7) (k := 2)
    (hk := by decide) (a := fun i => if i = 0 then -2 else 3) (ha := ?_) (c := -3)
  intro i
  split <;> decide
