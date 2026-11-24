/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Enumerative.RFubiniPeriodicity
import Mathlib.Tactic.NormNum

open MetaMathlibExt ArithmeticFunction

-- Modulo `4 = 2²`: `λ(4) = 2` and `R = 2`, so the `2`-Fubini numbers `1, 1, 2, 10, 62, 466, …`
-- repeat with period `2` modulo `4` from `n = 3` on.
example (n : ℕ) (hn : 3 ≤ n) :
    let rFubini : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1),
      Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < 2 → (j : ℕ) < 2 → f i = f j → i = j }
    rFubini (n + 2) ≡ rFubini n [MOD 4] := by
  have hcar : carmichael 4 = 2 := by
    simpa using carmichael_two_pow_of_le_two (n := 2) le_rfl
  have hfac : (4 : ℕ).factorization = Finsupp.single 2 2 := by
    simpa using Nat.prime_two.factorization_pow (k := 2)
  have hR : (4 : ℕ).factorization.support.sup (4 : ℕ).factorization = 2 := by
    rw [hfac, Finsupp.support_single _ two_ne_zero, Finset.sup_singleton,
      Finsupp.single_eq_same]
  have h := rFubini_add_carmichael_modEq 4 2 n (by norm_num) (by omega)
  rw [hcar] at h
  exact h

-- Modulo the prime `2`: `λ(2) = 1` and `R = 1`, so the parity of the `3`-Fubini numbers is
-- constant from `n = 3` on.
example (n : ℕ) (hn : 3 ≤ n) :
    let rFubini : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1),
      Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < 3 → (j : ℕ) < 3 → f i = f j → i = j }
    rFubini (n + 1) ≡ rFubini n [MOD 2] := by
  have hR : (2 : ℕ).factorization.support.sup (2 : ℕ).factorization = 1 := by
    rw [Nat.prime_two.factorization, Finsupp.support_single _ one_ne_zero,
      Finset.sup_singleton, Finsupp.single_eq_same]
  have h := rFubini_add_carmichael_modEq 2 3 n (by norm_num) (by omega)
  rw [carmichael_two] at h
  exact h

-- For `K = 0` the bound is `n ≥ r - 1` and `λ(0) = 0`, so the congruence is equality.
example (r n : ℕ) (hr : 1 ≤ r) (hn : r - 1 ≤ n) :
    let rFubini : ℕ → ℕ := fun m => ∑ k ∈ Finset.range (m + 1),
      Nat.card { f : Fin m → Fin k // Function.Surjective f ∧
        ∀ i j : Fin m, (i : ℕ) < r → (j : ℕ) < r → f i = f j → i = j }
    rFubini (n + carmichael 0) ≡ rFubini n [MOD 0] :=
  rFubini_add_carmichael_modEq 0 r n hr (by simpa using hn)
