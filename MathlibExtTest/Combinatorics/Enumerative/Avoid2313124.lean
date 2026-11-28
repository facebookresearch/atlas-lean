/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.Avoid2313124
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.Pi

open MathlibExt.Combinatorics.Enumerative.OddFibonacciWanted

-- Putting zero first leaves exactly the choices for the remaining three entries.
example :
    Nat.card {σ : Equiv.Perm (Fin 4) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧ σ 0 = 0} =
      Nat.card {σ : Equiv.Perm (Fin 3) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} := by
  simpa using card_avoid_231_3124_pos_zero 4 (by decide) 0 (by decide)

-- At the last allowed position, the suffix is a singleton and the factor is three.
example :
    Nat.card {σ : Equiv.Perm (Fin 4) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧ σ 2 = 0} = 3 := by
  have singleton {k : ℕ} (hk : 1 < k) (π : Fin k → Fin k) :
      ¬ HasPattern (Equiv.refl (Fin 1)) π := by
    rintro ⟨e, he, _⟩
    exact (Subsingleton.elim _ _ : e ⟨0, by omega⟩ = e ⟨1, hk⟩) |>.not_lt
      (he _ _ (show (⟨0, by omega⟩ : Fin k) < ⟨1, hk⟩ by exact Nat.zero_lt_one))
  have hcard := Nat.card_of_subsingleton
    (⟨Equiv.refl _, singleton (by decide) pat231, singleton (by decide) pat3124⟩ :
      {σ : Equiv.Perm (Fin 1) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124})
  simpa [hcard] using card_avoid_231_3124_pos_zero 4 (by decide) 2 (by decide)

-- Enumerate the permutations and test classical containment directly.
local instance {n k : ℕ} (σ : Equiv.Perm (Fin n)) (π : Fin k → Fin k) :
    Decidable (HasPattern σ π) := by
  unfold HasPattern
  infer_instance

local instance {n : ℕ} : Fintype (Equiv.Perm (Fin n)) := fintypePerm

-- The two initial counts, before either forbidden pattern can occur.
example : Nat.card {σ : Equiv.Perm (Fin 1) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} =
    Nat.fib 1 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

example : Nat.card {σ : Equiv.Perm (Fin 2) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} =
    Nat.fib 3 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

-- Size four is the first size where both patterns can occur.
example : Nat.card {σ : Equiv.Perm (Fin 4) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} =
    Nat.fib 7 := by
  rw [Nat.card_eq_fintype_card]
  decide +kernel

-- The length-four avoiders split into these four counts by position of zero.
example : ∀ j : Fin 4,
    Fintype.card {σ : Equiv.Perm (Fin 4) //
      ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧ σ j = 0} =
      (![5, 4, 3, 1] : Fin 4 → ℕ) j := by
  decide +kernel

-- With zero last, the only avoider is the reverse permutation.
example : ∀ σ : Equiv.Perm (Fin 4),
    (¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124 ∧ σ 3 = 0) ↔ σ = Fin.revPerm := by
  decide +kernel

-- Check the public theorem's signature independently of the enumeration tests.
example (n : ℕ) (hn : 1 ≤ n) :
    Nat.card {σ : Equiv.Perm (Fin n) // ¬ HasPattern σ pat231 ∧ ¬ HasPattern σ pat3124} =
      Nat.fib (2 * n - 1) :=
  card_avoid_231_3124 n hn
