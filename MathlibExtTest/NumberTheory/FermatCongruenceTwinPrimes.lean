/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.FermatCongruenceTwinPrimes

/-! # Tests for the Fermat-type characterizations of twin primes -/

open MetaMathlibExt

-- The smallest twin prime pair satisfies both congruences, for all coprime integer bases.
example : ∀ a : ℤ, IsCoprime a 15 → 2 * a ^ 4 ≡ 5 * a ^ 2 - 3 [ZMOD 15] :=
  (twinPrime_iff_forall_fermat_congruence (n := 3) (by decide) (by decide)
    (fun h ↦ h.2.1 (by decide)) (fun h ↦ h.2.1 (by decide))).1.mp ⟨by decide, by decide⟩

example : ∀ a : ℤ, IsCoprime a 15 → 3 * a ^ 4 ≡ 5 * a ^ 2 - 2 [ZMOD 15] :=
  (twinPrime_iff_forall_fermat_congruence (n := 3) (by decide) (by decide)
    (fun h ↦ h.2.1 (by decide)) (fun h ↦ h.2.1 (by decide))).2.mp ⟨by decide, by decide⟩

private lemma not_carmichael_nine : ¬Nat.IsCarmichaelNumber 9 := fun h ↦
  (by decide : ¬(2 ^ 9 ≡ 2 [MOD 9])) (h.2.2 2)

-- With a composite upper modulus, the coprime base `2` refutes the first test.
example : ¬(Nat.Prime 7 ∧ Nat.Prime (7 + 2)) := by
  intro hp
  have ha : IsCoprime (2 : ℤ) 63 := ⟨-31, 1, by decide⟩
  have h := twinPrime_iff_forall_fermat_congruence (n := 7) (by decide) (by decide)
    (fun hc ↦ hc.2.1 (by decide)) not_carmichael_nine
  exact (by decide : ¬(2 * 2 ^ 8 ≡ 9 * 2 ^ 2 - 7 [ZMOD 63])) (h.1.mp hp 2 ha)

-- With a composite lower modulus, the same base refutes the second test.
example : ¬(Nat.Prime 9 ∧ Nat.Prime (9 + 2)) := by
  intro hp
  have ha : IsCoprime (2 : ℤ) 99 := ⟨-49, 1, by decide⟩
  have h := twinPrime_iff_forall_fermat_congruence (n := 9) (by decide) (by decide)
    not_carmichael_nine (fun hc ↦ hc.2.1 (by decide))
  exact (by decide : ¬(9 * 2 ^ 10 ≡ 11 * 2 ^ 8 - 2 [ZMOD 99])) (h.2.mp hp 2 ha)

-- The reverse directions detect primality for `(3, 5)` from the universal congruences.
example (h : (∀ a : ℤ, IsCoprime a 15 → 2 * a ^ 4 ≡ 5 * a ^ 2 - 3 [ZMOD 15]) ∨
    (∀ a : ℤ, IsCoprime a 15 → 3 * a ^ 4 ≡ 5 * a ^ 2 - 2 [ZMOD 15])) :
    Nat.Prime 3 ∧ Nat.Prime 5 := by
  have ht := twinPrime_iff_forall_fermat_congruence (n := 3) (by decide) (by decide)
    (fun h ↦ h.2.1 (by decide)) (fun h ↦ h.2.1 (by decide))
  exact h.elim ht.1.mpr ht.2.mpr
