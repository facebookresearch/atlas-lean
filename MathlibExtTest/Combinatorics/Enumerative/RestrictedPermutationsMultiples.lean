/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RestrictedPermutationsMultiples

open MetaMathlibExt

-- The empty board has one permutation, including when there are several residue classes.
example : Nat.card {π : Equiv.Perm (Fin 0) //
    ∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-3, 0, 6} : Finset ℤ)} = 1 :=
  (card_strongPerms_multiples_eq_fibonacciP 3 2 0 0 (by decide) (by decide)).trans (by
    rw [show 0 + 1 = 1 by rfl, fibonacciP_eq_one 2 1 (by decide) (by decide)]
    simp)

-- For displacements −2, 0, and 4, the five positions split into classes of lengths
-- three and two. Only the longer class can have a nontrivial cycle.
example : Nat.card {π : Equiv.Perm (Fin 5) //
    ∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-2, 0, 4} : Finset ℤ)} = 2 :=
  (card_strongPerms_multiples_eq_fibonacciP 2 2 2 1 (by decide) (by decide)).trans (by
    have h₁ := fibonacciP_eq_one 2 1 (by decide) (by decide)
    have h₂ := fibonacciP_eq_one 2 2 (by decide) (by decide)
    have h₃ : fibonacciP 2 3 = 1 := by
      rw [fibonacciP_rec 2 3 (by decide)]
      change fibonacciP 2 2 + fibonacciP 2 0 = 1
      simp [h₂]
    have h₄ : fibonacciP 2 4 = 2 := by
      rw [fibonacciP_rec 2 4 (by decide)]
      change fibonacciP 2 3 + fibonacciP 2 1 = 2
      rw [h₃, h₁]
    change fibonacciP 2 3 ^ 1 * fibonacciP 2 4 ^ 1 = 2
    simp [h₃, h₄])

-- With displacements −1, 0, and 1 there are eight permutations given by disjoint adjacent swaps.
example : Nat.card {π : Equiv.Perm (Fin 5) //
    ∀ x, ((π x : ℕ) : ℤ) - (x : ℕ) ∈ ({-1, 0, 1} : Finset ℤ)} = 8 :=
  (card_strongPerms_multiples_eq_fibonacciP 1 1 5 0 (by decide) (by decide)).trans (by
    rw [fibonacciP_one, fibonacciP_one]
    decide)
