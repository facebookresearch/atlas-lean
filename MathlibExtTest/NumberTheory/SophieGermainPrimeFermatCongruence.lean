/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.SophieGermainPrimeFermatCongruence

/-! # Tests for the Fermat-type characterizations of Sophie Germain primes -/

open MetaMathlibExt

-- The characterizations include the even prime `2`; both congruences hold modulo `10`.
example : ∀ a : ℤ, IsCoprime a 10 → a ^ 4 ≡ 5 * a ^ 3 - 4 [ZMOD 10] :=
  (isSophieGermainPrime_iff_forall_fermat_congruence Nat.prime_two).1.mp
    ⟨Nat.prime_two, by decide⟩

example : ∀ a : ℤ, IsCoprime a 10 → 5 * a ≡ 2 * a ^ 4 + 3 [ZMOD 10] := by
  have h : ∀ a : ℤ, IsCoprime a 10 → 5 * a ^ 1 ≡ 2 * a ^ 4 + 2 + 1 [ZMOD 10] :=
    (isSophieGermainPrime_iff_forall_fermat_congruence Nat.prime_two).2.mp
      ⟨Nat.prime_two, by decide⟩
  simpa only [pow_one, add_assoc, show (2 : ℤ) + 1 = 3 by decide] using h

-- At `p = 7`, the coprime base `2` disproves each congruence independently.
example : ¬Nat.IsSophieGermainPrime 7 := by
  intro h
  have ha : IsCoprime (2 : ℤ) 105 := ⟨-52, 1, by decide⟩
  exact (by decide : ¬(2 ^ 14 ≡ 15 * 2 ^ 8 - 14 [ZMOD 105]))
    ((isSophieGermainPrime_iff_forall_fermat_congruence (by decide : Nat.Prime 7)).1.mp h 2 ha)

example : ¬Nat.IsSophieGermainPrime 7 := by
  intro h
  have ha : IsCoprime (2 : ℤ) 105 := ⟨-52, 1, by decide⟩
  exact (by decide : ¬(15 * 2 ^ 6 ≡ 7 * 2 ^ 14 + 7 + 1 [ZMOD 105]))
    ((isSophieGermainPrime_iff_forall_fermat_congruence (by decide : Nat.Prime 7)).2.mp h 2 ha)
