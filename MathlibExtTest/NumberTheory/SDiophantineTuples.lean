/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SDiophantineTuples

namespace MetaMathlibExt

-- The allowed prime set may contain primes that do not occur.
example : IsSDiophantineTuple {5, 7} {1, 4} := by
  refine ⟨by decide, ?_⟩
  intro a ha b hb hab
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb
  have h5 : (5 : ℕ).primeFactors ⊆ {5, 7} := by
    have h : (5 ^ 1 : ℕ).primeFactors = {5} :=
      Nat.primeFactors_prime_pow (by decide) Nat.prime_five
    rw [pow_one] at h
    simp [h]
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;>
    first | exact (hab rfl).elim | exact h5

-- A prime factor outside the allowed set rules out the pair.
example : ¬IsSDiophantineTuple {5, 7} {1, 5} := by
  intro h
  have h2 : 2 ∈ (1 * 5 + 1 : ℕ).primeFactors :=
    Nat.mem_primeFactors.mpr ⟨Nat.prime_two, by decide, by decide⟩
  have hmem : 2 ∈ ({5, 7} : Finset ℕ) := h.2 1 (by simp) 5 (by simp) (by decide) h2
  exact (by decide : 2 ∉ ({5, 7} : Finset ℕ)) hmem

-- The theorem specializes to the smallest primes allowed by its congruence and size conditions.
example {a b c d : ℕ} (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hS : IsSDiophantineTuple {7, 5} {a, b, c, d})
    (hcase : padicValNat 7 (a * d + 1) = 0 ∧ padicValNat 7 (b * c + 1) = 0 ∧
      0 < padicValNat 7 (a * b + 1) ∧ padicValNat 7 (a * b + 1) = padicValNat 7 (a * c + 1) ∧
      padicValNat 7 (a * c + 1) < padicValNat 7 (b * d + 1) ∧
      padicValNat 7 (b * d + 1) < padicValNat 7 (c * d + 1) ∧
      0 < padicValNat 5 (a * b + 1) ∧ padicValNat 5 (a * b + 1) = padicValNat 5 (c * d + 1) ∧
      padicValNat 5 (c * d + 1) < padicValNat 5 (a * c + 1) ∧
      padicValNat 5 (a * c + 1) = padicValNat 5 (b * d + 1) ∧
      padicValNat 5 (b * d + 1) < padicValNat 5 (a * d + 1) ∧
      padicValNat 5 (b * d + 1) < padicValNat 5 (b * c + 1)) :
    (b : ℝ) < 1042 / 1000 * (5 : ℝ) ^ (padicValNat 5 (a * c + 1) - padicValNat 5 (a * b + 1)) :=
  sDiophantine_quadruple_caseIV_bound (p := 7) (q := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) hab hbc hcd hS hcase

#print axioms sDiophantine_quadruple_caseIV_bound

end MetaMathlibExt
