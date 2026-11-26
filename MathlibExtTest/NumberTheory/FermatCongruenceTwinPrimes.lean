/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FermatCongruenceTwinPrimes

open MetaMathlibExt

-- The proved statement, restated at a general `n`.
example {n : ℕ} (hodd : Odd n) (hn : 3 ≤ n) (hnc : ¬Nat.IsCarmichaelNumber n)
    (hn2c : ¬Nat.IsCarmichaelNumber (n + 2)) :
    ((n.Prime ∧ (n + 2).Prime) ↔ ∀ a : ℤ, IsCoprime a ((n : ℤ) * (n + 2)) →
        2 * a ^ (n + 1) ≡ (n + 2) * a ^ 2 - n [ZMOD (n : ℤ) * (n + 2)]) ∧
      ((n.Prime ∧ (n + 2).Prime) ↔ ∀ a : ℤ, IsCoprime a ((n : ℤ) * (n + 2)) →
        n * a ^ (n + 1) ≡ (n + 2) * a ^ (n - 1) - 2 [ZMOD (n : ℤ) * (n + 2)]) :=
  twinPrime_iff_forall_fermat_congruence hodd hn hnc hn2c

-- At `n = 3`, the twin primes `3` and `5` satisfy the first congruence for `a = 2`.
example : 2 * (2 : ℤ) ^ (3 + 1) ≡ ((3 : ℤ) + 2) * (2 : ℤ) ^ 2 - (3 : ℤ)
    [ZMOD (3 : ℤ) * ((3 : ℤ) + 2)] := by
  have hnc3 : ¬Nat.IsCarmichaelNumber 3 := fun h ↦ h.2.1 (by decide)
  have hnc5 : ¬Nat.IsCarmichaelNumber 5 := fun h ↦ h.2.1 (by decide)
  have hcop : IsCoprime (2 : ℤ) ((3 : ℤ) * ((3 : ℤ) + 2)) := ⟨8, -1, by norm_num⟩
  exact (twinPrime_iff_forall_fermat_congruence (n := 3) (by decide) (by decide)
    hnc3 hnc5).1.mp ⟨by decide, by decide⟩ 2 hcop

-- At `n = 3`, the twin primes `3` and `5` satisfy the second congruence for `a = 2`.
example : (3 : ℤ) * (2 : ℤ) ^ (3 + 1) ≡ ((3 : ℤ) + 2) * (2 : ℤ) ^ (3 - 1) - 2
    [ZMOD (3 : ℤ) * ((3 : ℤ) + 2)] := by
  have hnc3 : ¬Nat.IsCarmichaelNumber 3 := fun h ↦ h.2.1 (by decide)
  have hnc5 : ¬Nat.IsCarmichaelNumber 5 := fun h ↦ h.2.1 (by decide)
  have hcop : IsCoprime (2 : ℤ) ((3 : ℤ) * ((3 : ℤ) + 2)) := ⟨8, -1, by norm_num⟩
  exact (twinPrime_iff_forall_fermat_congruence (n := 3) (by decide) (by decide)
    hnc3 hnc5).2.mp ⟨by decide, by decide⟩ 2 hcop

-- At `n = 9`, the first congruence fails for some coprime base, since `9` is not prime.
example : ¬∀ a : ℤ, IsCoprime a ((9 : ℤ) * ((9 : ℤ) + 2)) →
    2 * a ^ (9 + 1) ≡ ((9 : ℤ) + 2) * a ^ 2 - (9 : ℤ)
      [ZMOD (9 : ℤ) * ((9 : ℤ) + 2)] := by
  have hnc9 : ¬Nat.IsCarmichaelNumber 9 := fun h ↦ absurd (h.2.2 3) (by decide)
  have hnc11 : ¬Nat.IsCarmichaelNumber 11 := fun h ↦ h.2.1 (by decide)
  intro H
  have hprimes := (twinPrime_iff_forall_fermat_congruence (n := 9) (by decide)
    (by decide) hnc9 hnc11).1.mpr H
  exact (by decide : ¬Nat.Prime 9) hprimes.1
