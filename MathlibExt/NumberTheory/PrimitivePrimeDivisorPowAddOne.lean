/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Group.Int.Defs
public import MathlibExt.NumberTheory.PrimitiveDivisor
import MathlibExt.NumberTheory.BangZsigmondy
import Mathlib.FieldTheory.Finite.Basic

/-!
# Primitive prime factors of `a ^ n + 1`

A primitive prime divisor of `a ^ (2 * n) - 1` gives a prime modulo which `a` has order
`2 * n`. Its `n`-th power is therefore `-1`, and no earlier positive power is `-1`.
-/

namespace MetaMathlibExt

/-- **Primitive prime factors of $a^n + 1$.** Let $a \ge 2$ and $n \ge 1$ be integers with
$(a, n) \ne (2, 3)$, and if $n = 1$ suppose that $a + 1$ is not a power of $2$. Then $a^n + 1$
has a primitive prime factor $p$, that is, a prime $p$ that divides $a^n + 1$ but divides no
$a^m + 1$ with $1 \le m < n$, such that $p \equiv 1 \pmod{2n}$.

The second exception is not in the printed statement: for $a = 3$, $n = 1$ the only prime factor
of $3 + 1 = 4$ is $2 \not\equiv 1 \pmod 2$; the paper's proof applies Lemma 2.3 to
$a^{2n} - 1$, whose exceptions include exactly this case.

Source: Tomohiro Yamada, *Determining all Biunitary Triperfect Numbers of a Certain Form*,
Journal of Integer Sequences 28 (2025), Article 25.4.5, Lemma 5 (`jis-2025-25.4.5-lem-5`). -/
public theorem exists_primitivePrimeDivisor_pow_add_one (a n : ℕ) (ha : 2 ≤ a)
    (hn : 1 ≤ n) (hexc : ¬ (a = 2 ∧ n = 3)) (hexc' : ¬ (n = 1 ∧ ∃ k : ℕ, a + 1 = 2 ^ k)) :
    ∃ p, IntegerSequence.IsPrimitivePrimeDivisor (fun m => (a : ℤ) ^ m + 1) n p ∧
      p % (2 * n) = 1 := by
  have hnexc : ¬ IsBangZsigmondyExceptional a 1 (2 * n) := by
    rintro (⟨ha2, _, h6⟩ | ⟨h2, hpow⟩)
    · exact hexc ⟨ha2, by omega⟩
    · exact hexc' ⟨by omega, hpow⟩
  obtain ⟨p, hp⟩ := bangZsigmondy_exists_primitivePrimeDivisor (by decide : 0 < 1)
    (by omega : 1 < a) (Nat.coprime_one_right a) (by omega : 2 ≤ 2 * n) hnexc
  have : Fact p.Prime := ⟨hp.prime⟩
  have sub_iff (m : ℕ) : (p : ℤ) ∣ (a : ℤ) ^ m - (1 : ℤ) ^ m ↔
      (a : ZMod p) ^ m = 1 := by
    simp [← ZMod.intCast_zmod_eq_zero_iff_dvd, sub_eq_zero]
  have add_iff (m : ℕ) : (p : ℤ) ∣ (a : ℤ) ^ m + 1 ↔ (a : ZMod p) ^ m = -1 := by
    simp [← ZMod.intCast_zmod_eq_zero_iff_dvd, eq_neg_iff_add_eq_zero]
  have hpow := (sub_iff _).mp hp.dvd
  have hmin (m : ℕ) (hm : 0 < m) (hlt : m < 2 * n) : (a : ZMod p) ^ m ≠ 1 :=
    fun h => hp.not_dvd_of_lt hm hlt ((sub_iff m).mpr h)
  have hord : orderOf (a : ZMod p) = 2 * n :=
    (orderOf_eq_iff (by omega)).mpr ⟨hpow, fun m hlt hm => hmin m hm hlt⟩
  refine ⟨p, ⟨hp.prime, hn, hp.two_le, (add_iff n).mpr ?_, ?_⟩, ?_⟩
  · have hsq : ((a : ZMod p) ^ n) ^ 2 = 1 := by rwa [← pow_mul, mul_comm n]
    exact (sq_eq_one_iff.mp hsq).resolve_left (hmin n hn (by omega))
  · intro m hm hlt hdvd
    apply hmin (2 * m) (by omega) (by omega)
    rw [mul_comm 2 m, pow_mul, (add_iff m).mp hdvd, neg_one_sq]
  · have ha0 : (a : ZMod p) ≠ 0 := by
      intro h
      simp [h] at hord
      omega
    have hdvd := ZMod.orderOf_dvd_card_sub_one ha0
    rw [hord] at hdvd
    have hmod := (Nat.modEq_of_dvd' hp.prime.one_le hdvd).symm
    simpa [Nat.ModEq, Nat.mod_eq_of_lt (by omega : 1 < 2 * n)] using hmod

end MetaMathlibExt
