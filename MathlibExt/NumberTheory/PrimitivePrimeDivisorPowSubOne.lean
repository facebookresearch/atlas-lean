/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.PrimitiveDivisor

import Mathlib.FieldTheory.Finite.Basic
import Mathlib.GroupTheory.OrderOfElement

/-! # Primitive divisors of a power minus one

The primitive index is the multiplicative order of the base in the prime residue field.
-/

namespace MetaMathlibExt

-- The source's bound on the base is retained in the signature. Primitivity already ensures
-- that its residue is nonzero.
set_option linter.unusedVariables false in
/-- **Primitive prime divisors of $a^n - 1$ are $1$ modulo $n$.** Let $a \ge 2$ and $n \ge 2$ be
natural numbers, and let $p$ be a primitive prime divisor of the integer sequence $m \mapsto
a^m - 1$ at index $n$, that is, a prime that divides $a^n - 1$ and divides no $a^m - 1$ with
$1 \le m < n$. Then $p \equiv 1 \pmod n$.

This is the congruence half of Bang's theorem. Its existence half (such a $p$ exists unless
$(a, n) = (2, 6)$, or $n = 2$ and $a + 1$ is a power of $2$) is the case $b = 1$ of the
Bang–Zsigmondy theorem.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 4 (`jis-2025-25.4.5-lem-4`),
quoting Bang. -/
public theorem primitivePrimeDivisor_pow_sub_one_mod_eq_one (a n p : ℕ) (ha : 2 ≤ a)
    (hn : 2 ≤ n)
    (hp : IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m - 1) n p) :
    p % n = 1 := by
  let : Fact p.Prime := ⟨hp.prime⟩
  let z : ZMod p := a
  have hcast (k : ℕ) : z ^ k = 1 ↔ (p : ℤ) ∣ (a : ℤ) ^ k - 1 := by
    rw [eq_comm]
    simpa only [Int.cast_one, Int.cast_pow, Int.cast_natCast, z] using
      ZMod.intCast_eq_intCast_iff_dvd_sub 1 ((a : ℤ) ^ k) p
  have hpow : z ^ n = 1 := (hcast n).mpr hp.dvd
  have hn' : 0 < n := by omega
  have horder_pos : 0 < orderOf z :=
    orderOf_pos_iff.mpr (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn', hpow⟩)
  have horder : orderOf z = n := by
    have hle := orderOf_le_of_pow_eq_one hn' hpow
    by_contra hne
    exact hp.not_dvd_of_lt horder_pos (lt_of_le_of_ne hle hne)
      ((hcast _).mp (pow_orderOf_eq_one z))
  have hz : z ≠ 0 := by
    intro hz
    rw [hz, zero_pow hn'.ne'] at hpow
    exact zero_ne_one hpow
  have hdiv : n ∣ p - 1 := horder ▸ orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one hz)
  have h1p : 1 ≤ p := le_trans (by decide : 1 ≤ 2) hp.two_le
  have h1n : 1 < n := by omega
  simpa only [Nat.ModEq, Nat.mod_eq_of_lt h1n] using
    ((Nat.modEq_iff_dvd' h1p).mpr hdiv).symm

end MetaMathlibExt
