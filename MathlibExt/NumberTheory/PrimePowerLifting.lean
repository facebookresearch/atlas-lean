/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Prime.Defs
import Mathlib.NumberTheory.Basic

@[expose] public section

namespace MetaMathlibExt

/-- **Lifting a congruence to one along powers of the modulus.** Let $p$, $n$ and $a$ be natural
numbers. If $a \equiv 1 \pmod p$, then $a^{p^n} \equiv 1 \pmod{p^{n+1}}$.

The modulus $p$ need not be prime. -/
theorem pow_pow_modEq_one_of_modEq_one (p n a : ℕ) (h : Nat.ModEq p a 1) :
    Nat.ModEq (p ^ (n + 1)) (a ^ (p ^ n)) 1 := by
  rw [Nat.modEq_iff_dvd] at h ⊢
  simpa using dvd_sub_pow_of_dvd_sub h n

set_option linter.unusedVariables false in
/--
**Prime-power lifting of a congruence to one.** Let $p$ be a prime and let $n$ and $a$ be
positive integers. If $a \equiv 1 \pmod p$, then $a^{p^n} \equiv 1 \pmod{p^{n+1}}$.

Source: Hacène Belbachir and Celia Salhi, "The Generalized Bi-Periodic
Fibonacci Sequence Modulo m," Journal of Integer Sequences 24 (2021),
Article 21.9.4, Theorem (label th4), lines 340–341,
<https://cs.uwaterloo.ca/journals/JIS/VOL24/Salhi/salhi4.tex>.
It follows from `pow_pow_modEq_one_of_modEq_one`; the hypotheses `hp`, `hn` and `ha` are
unused and keep the source's shape.
Proves `Wanted` entry `prime_power_lifting_modEq_one`.
-/
theorem prime_power_lifting_modEq_one
    (p n a : ℕ) (hp : Nat.Prime p) (hn : 0 < n) (ha : 0 < a)
    (h : Nat.ModEq p a 1) :
    Nat.ModEq (p ^ (n + 1)) (a ^ (p ^ n)) 1 := by
  exact pow_pow_modEq_one_of_modEq_one p n a h

end MetaMathlibExt
