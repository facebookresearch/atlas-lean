/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.LinearCombination

/-!
# Fermat's congruence for a product of coprime moduli

Theorem 1.1 (a) of Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025),
Article A31. Let `n` and `m` be coprime natural numbers with `0 < n < m`. Then `m - n` is a unit
modulo `n * m`, and the paper's fraction `(a ^ (m - n) - 1) / (m - n)` is read in `ZMod (n * m)`
as multiplication by the inverse of `m - n`.

The second of the two equalities holds for every integer `a`, because `n - m` is the negative of
the unit `m - n`. Multiplied by `m - n`, the first equality becomes the congruence
`(m - n) a ^ (m - 1) ≡ (a ^ (m - n) - 1) n + (m - n) a ^ (m - n) [ZMOD n * m]`. For `a` coprime
to `n * m`, it holds modulo `n` exactly when `a ^ (n - 1) ≡ 1 [ZMOD n]`, and modulo `m` exactly
when `a ^ (m - 1) ≡ 1 [ZMOD m]`. By the Chinese remainder theorem, an integer coprime to `n`
agrees modulo `n` with an integer coprime to `n * m`, and likewise for `m`.
-/

namespace MetaMathlibExt

/-- Modulo `n`, the cleared first equality is Fermat's congruence for `n`. -/
private lemma fermatCoprimeModuli_modEq_left_iff {n m : ℕ} (hn : 0 < n) (hnm : n < m)
    (hcop : Nat.Coprime n m) {a : ℤ} (ha : IsCoprime a (n : ℤ)) :
    ((m : ℤ) - n) * a ^ (m - 1) ≡ (a ^ (m - n) - 1) * n + ((m : ℤ) - n) * a ^ (m - n)
        [ZMOD n] ↔ a ^ (n - 1) ≡ 1 [ZMOD n] := by
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_self]
  have hA : IsUnit (a : ZMod n) := (ZMod.coe_int_isUnit_iff_isCoprime a n).mpr ha.symm
  have hM : IsUnit (m : ZMod n) := (ZMod.isUnit_iff_coprime m n).mpr hcop.symm
  have hexp : m - 1 = (m - n) + (n - 1) := by omega
  rw [hexp, pow_add, sub_zero, mul_zero, zero_add, hM.mul_right_inj,
    ← (hA.pow (m - n)).mul_right_inj (c := 1), mul_one]

/-- Modulo `m`, the cleared first equality is Fermat's congruence for `m`. -/
private lemma fermatCoprimeModuli_modEq_right_iff {n m : ℕ} (hcop : Nat.Coprime n m) (a : ℤ) :
    ((m : ℤ) - n) * a ^ (m - 1) ≡ (a ^ (m - n) - 1) * n + ((m : ℤ) - n) * a ^ (m - n)
        [ZMOD m] ↔ a ^ (m - 1) ≡ 1 [ZMOD m] := by
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_self]
  have hN : IsUnit (n : ZMod m) := (ZMod.isUnit_iff_coprime n m).mpr hcop
  rw [← hN.mul_right_inj (b := (a : ZMod m) ^ (m - 1)) (c := 1)]
  constructor <;> intro h <;> linear_combination -h

/-- For one integer `a` coprime to `n * m`, the two equalities in `ZMod (n * m)` hold if and only
if `a ^ (n - 1) ≡ 1 [ZMOD n]` and `a ^ (m - 1) ≡ 1 [ZMOD m]`. -/
private lemma fermatCoprimeModuli_eqns_iff {n m : ℕ} (hn : 0 < n) (hnm : n < m)
    (hcop : Nat.Coprime n m) {a : ℤ} (ha : IsCoprime a ((n : ℤ) * m)) :
    ((a : ZMod (n * m)) ^ (m - 1) =
            ((a : ZMod (n * m)) ^ (m - n) - 1) * ((m - n : ℕ) : ZMod (n * m))⁻¹ * n +
              (a : ZMod (n * m)) ^ (m - n) ∧
          ((a : ZMod (n * m)) ^ (m - n) - 1) * ((m - n : ℕ) : ZMod (n * m))⁻¹ * n +
              (a : ZMod (n * m)) ^ (m - n) =
            ((a : ZMod (n * m)) ^ (m - n) - 1) * ((m - n : ℕ) : ZMod (n * m))⁻¹ * m + 1) ↔
      a ^ (n - 1) ≡ 1 [ZMOD n] ∧ a ^ (m - 1) ≡ 1 [ZMOD m] := by
  have hd : Nat.Coprime (m - n) (n * m) :=
    Nat.Coprime.mul_right ((Nat.coprime_sub_self_left hnm.le).mpr hcop.symm)
      ((Nat.coprime_self_sub_left hnm.le).mpr hcop)
  have hu := ZMod.coe_mul_inv_eq_one (m - n) hd
  set u := ((m - n : ℕ) : ZMod (n * m))⁻¹
  rw [Nat.cast_sub hnm.le] at hu
  set x := (a : ZMod (n * m))
  have h2 : (x ^ (m - n) - 1) * u * n + x ^ (m - n) = (x ^ (m - n) - 1) * u * m + 1 := by
    linear_combination (1 - x ^ (m - n)) * hu
  have h1 : x ^ (m - 1) = (x ^ (m - n) - 1) * u * n + x ^ (m - n) ↔
      ((m : ℤ) - n) * a ^ (m - 1) ≡ (a ^ (m - n) - 1) * n + ((m : ℤ) - n) * a ^ (m - n)
        [ZMOD ((n * m : ℕ) : ℤ)] := by
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    constructor <;> intro h
    · linear_combination ((m : ZMod (n * m)) - n) * h + (x ^ (m - n) - 1) * n * hu
    · linear_combination u * h + (x ^ (m - n) - x ^ (m - 1)) * hu
  rw [and_iff_left h2, h1, Nat.cast_mul,
    ← Int.modEq_and_modEq_iff_modEq_mul (by simpa using hcop),
    fermatCoprimeModuli_modEq_left_iff hn hnm hcop ha.of_mul_right_left,
    fermatCoprimeModuli_modEq_right_iff hcop]

/-- **Fermat's congruence for a product of coprime moduli.** Let $n$ and $m$ be coprime natural
numbers with $0 < n < m$. Since $\gcd(m - n, nm) = 1$, the residue of $m - n$ is invertible in
$\mathbb{Z}/nm\mathbb{Z}$; write $u$ for its inverse. Then the equalities
$a^{m-1} = (a^{m-n} - 1)\,u\,n + a^{m-n}$ and
$(a^{m-n} - 1)\,u\,n + a^{m-n} = (a^{m-n} - 1)\,u\,m + 1$ in $\mathbb{Z}/nm\mathbb{Z}$ hold for
every integer $a$ coprime to $nm$ if and only if both $n$ and $m$ have the Fermat property: for
$k = n$ and for $k = m$, $a^{k-1} \equiv 1 \pmod{k}$ for every integer $a$ coprime to $k$.

This is the source's congruence
$a^{m-1} \equiv \frac{a^{m-n} - 1}{m - n}\,n + a^{m-n} \equiv \frac{a^{m-n} - 1}{m - n}\,m + 1
\pmod{nm}$, with the division by $m - n$ read as multiplication by $u$.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 1.1 (a) (`integers-2025-A31-thm-1-1`). -/
public theorem forall_fermat_congruence_iff_of_coprime {n m : ℕ} (hn : 0 < n)
    (hnm : n < m) (hcop : Nat.Coprime n m) :
    (∀ a : ℤ, IsCoprime a ((n : ℤ) * m) →
        ((a : ZMod (n * m)) ^ (m - 1) =
            ((a : ZMod (n * m)) ^ (m - n) - 1) * ((m - n : ℕ) : ZMod (n * m))⁻¹ * n +
              (a : ZMod (n * m)) ^ (m - n) ∧
          ((a : ZMod (n * m)) ^ (m - n) - 1) * ((m - n : ℕ) : ZMod (n * m))⁻¹ * n +
              (a : ZMod (n * m)) ^ (m - n) =
            ((a : ZMod (n * m)) ^ (m - n) - 1) * ((m - n : ℕ) : ZMod (n * m))⁻¹ * m + 1)) ↔
      (∀ a : ℤ, IsCoprime a (n : ℤ) → a ^ (n - 1) ≡ 1 [ZMOD n]) ∧
        (∀ a : ℤ, IsCoprime a (m : ℤ) → a ^ (m - 1) ≡ 1 [ZMOD m]) := by
  constructor
  · intro H
    obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hcop
    constructor
    · intro a ha
      -- `b = a + n (s - a s)` is congruent to `a` modulo `n` and to `1` modulo `m`.
      have hb : a + n * (s - a * s) = 1 + m * (a * t - t) := by
        linear_combination (1 - a) * hst
      have hbcop : IsCoprime (a + n * (s - a * s)) ((n : ℤ) * m) :=
        (ha.add_mul_left_left _).mul_right (hb ▸ isCoprime_one_left.add_mul_left_left _)
      have hab : a ≡ a + n * (s - a * s) [ZMOD n] :=
        Int.modEq_iff_dvd.mpr ⟨s - a * s, by ring⟩
      exact (hab.pow _).trans ((fermatCoprimeModuli_eqns_iff hn hnm hcop hbcop).mp
        (H _ hbcop)).1
    · intro a ha
      -- `c = a + m (t - a t)` is congruent to `1` modulo `n` and to `a` modulo `m`.
      have hc : a + m * (t - a * t) = 1 + n * (a * s - s) := by
        linear_combination (1 - a) * hst
      have hccop : IsCoprime (a + m * (t - a * t)) ((n : ℤ) * m) :=
        (hc ▸ isCoprime_one_left.add_mul_left_left _).mul_right (ha.add_mul_left_left _)
      have hac : a ≡ a + m * (t - a * t) [ZMOD m] :=
        Int.modEq_iff_dvd.mpr ⟨t - a * t, by ring⟩
      exact (hac.pow _).trans ((fermatCoprimeModuli_eqns_iff hn hnm hcop hccop).mp
        (H _ hccop)).2
  · rintro ⟨Hn, Hm⟩ a ha
    exact (fermatCoprimeModuli_eqns_iff hn hnm hcop ha).mpr
      ⟨Hn a ha.of_mul_right_left, Hm a ha.of_mul_right_right⟩

end MetaMathlibExt
