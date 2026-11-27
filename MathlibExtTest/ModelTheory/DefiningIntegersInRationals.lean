/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.ModelTheory.DefiningIntegersInRationals
import Mathlib.Data.Rat.Lemmas

/-!
# Tests for Robinson's definition of the integers in the rationals
-/

@[expose] public section

namespace DefiningIntegersInRationalsTest

open MathlibExt.ModelTheory.DefiningIntegersInRationalsWanted

/-- The theorem with the source's binders: `N` is an integer iff it satisfies Robinson's formula
for all `A` and `B`. -/
example (N : ℚ) :
    N ∈ Set.range ((↑) : ℤ → ℚ) ↔
      ∀ A B : ℚ,
        ((∃ X Y Z : ℚ, 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) ∧
            ∀ M : ℚ, (∃ X Y Z : ℚ, 2 + A * B * M ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) →
              ∃ X Y Z : ℚ, 2 + A * B * (M + 1) ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) →
          ∃ X Y Z : ℚ, 2 + A * B * N ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2 :=
  mem_range_intCast_iff_robinson N

/-- The integer `-3` satisfies Robinson's formula. -/
example : ∀ A B : ℚ,
    ((∃ X Y Z : ℚ, 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) ∧
        ∀ M : ℚ, (∃ X Y Z : ℚ, 2 + A * B * M ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) →
          ∃ X Y Z : ℚ, 2 + A * B * (M + 1) ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) →
      ∃ X Y Z : ℚ, 2 + A * B * (-3) ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2 :=
  (mem_range_intCast_iff_robinson (-3)).mp ⟨-3, by push_cast; rfl⟩

/-- The rational `1 / 2` does not satisfy Robinson's formula: some `A`, `B` satisfy its
hypothesis but not its conclusion at `N = 1 / 2`. -/
example : ¬∀ A B : ℚ,
    ((∃ X Y Z : ℚ, 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) ∧
        ∀ M : ℚ, (∃ X Y Z : ℚ, 2 + A * B * M ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) →
          ∃ X Y Z : ℚ, 2 + A * B * (M + 1) ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2) →
      ∃ X Y Z : ℚ, 2 + A * B * (1 / 2) ^ 2 + B * Z ^ 2 = X ^ 2 + A * Y ^ 2 := by
  rw [← mem_range_intCast_iff_robinson]
  rintro ⟨n, hn⟩
  have h := congrArg Rat.den hn
  simp [one_div] at h

end DefiningIntegersInRationalsTest
