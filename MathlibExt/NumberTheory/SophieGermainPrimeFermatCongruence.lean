/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Coprime.Basic
public import MathlibExt.NumberTheory.SophieGermainPrime
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Carmichael
import Mathlib.Tactic.LinearCombination

/-!
# Fermat-type characterizations of Sophie Germain primes

For a prime `p`, each cleared congruence modulo `p * (2 * p + 1)` is equivalent to the
Fermat congruence modulo `2 * p + 1`. The Carmichael function rules out a composite
`2 * p + 1` satisfying this congruence at every coprime base.

## References

* Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
  pp. 1–10, Theorem 3.3. The reduction of each congruence to the Fermat property follows Agoh.
* Adel Alahmadi and Florian Luca, *There are no Carmichael numbers of the form $2^n p + 1$
  with $p$ prime*, C. R. Mathématique 360 (2022), pp. 1177–1181, Theorem 3. Agoh invokes their
  theorem to exclude Carmichael numbers of the form $2p + 1$. This proof establishes the needed
  $2p + 1$ case directly using the exponent of the group of units.
-/

namespace MetaMathlibExt

/-- The Fermat property detects primality for numbers of the form `2 * p + 1`. -/
private lemma prime_two_mul_add_one_iff_fermat {p : ℕ} (hp : p.Prime) :
    (2 * p + 1).Prime ↔ ∀ a : ℤ, IsCoprime a ((2 * p + 1 : ℕ) : ℤ) →
      a ^ (2 * p) ≡ 1 [ZMOD ((2 * p + 1 : ℕ) : ℤ)] := by
  let m := 2 * p + 1
  refine ⟨fun hm a ha ↦ ?_, fun h ↦ ?_⟩
  · simpa only [Nat.add_sub_cancel] using Int.ModEq.pow_card_sub_one_eq_one hm ha
  by_cases hp2 : p = 2
  · subst p
    decide
  by_contra hm
  have hpLe := hp.two_le
  have hm0 : m ≠ 0 := by omega
  let _ : NeZero m := ⟨hm0⟩
  change ∀ a : ℤ, IsCoprime a (m : ℤ) → a ^ (2 * p) ≡ 1 [ZMOD (m : ℤ)] at h
  have hc : ArithmeticFunction.carmichael m ∣ 2 * p := by
    rw [ArithmeticFunction.carmichael_eq_exponent hm0, Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro u
    let a : ℤ := (u : ZMod m).val
    have ha : (a : ZMod m) = u := by
      rw [show a = ((u : ZMod m).val : ℤ) from rfl, Int.cast_natCast, ZMod.natCast_zmod_val]
    have hcop : IsCoprime a (m : ℤ) :=
      ((ZMod.isUnit_intCast_iff_isCoprime a m).mp (ha ▸ u.isUnit)).symm
    apply Units.ext
    simpa only [Int.cast_pow, Int.cast_one, ha, Units.val_pow_eq_pow_val, Units.val_one] using
      (ZMod.intCast_eq_intCast_iff _ _ m).mpr (h a hcop)
  -- Every prime divisor `r` is odd, and `r - 1` divides `2 * p`.
  have hdivisor (r : ℕ) (hr : r.Prime) (hrm : r ∣ m) : r = 3 := by
    have hr2 : r ≠ 2 := by
      rintro rfl
      omega
    obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
    have hd := (ArithmeticFunction.carmichael_dvd hrm).trans hc
    rw [ArithmeticFunction.carmichael_of_prime hr, show r - 1 = 2 * k by omega] at hd
    have hkp := Nat.dvd_of_mul_dvd_mul_left (by decide : 0 < 2) hd
    rcases hp.eq_one_or_self_of_dvd k hkp with h1 | heq
    · omega
    · have hrEq : r = m := by omega
      exact (hm (show m.Prime from hrEq ▸ hr)).elim
  obtain ⟨r, hr, hrm⟩ := Nat.exists_prime_and_dvd (show m ≠ 1 by omega)
  have h3 : 3 ∣ m := hdivisor r hr hrm ▸ hrm
  obtain ⟨d, hd⟩ := h3
  obtain ⟨s, hs, hsd⟩ := Nat.exists_prime_and_dvd (show d ≠ 1 by omega)
  have hsm : s ∣ m := hd ▸ dvd_mul_of_dvd_right hsd 3
  rw [hdivisor s hs hsm] at hsd
  have h9 : 3 ^ 2 ∣ m := by
    rw [hd, pow_two]
    exact Nat.mul_dvd_mul_left 3 hsd
  -- Since all prime factors are `3` and `m > 3`, `9` divides `m`. Its unit group
  -- has exponent `6`, so `3` divides `2 * p`, contradicting `3 ∣ 2 * p + 1`.
  have hc3 : 3 ∣ ArithmeticFunction.carmichael (3 ^ 2) := by
    rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two 2 (by decide : Nat.Prime 3) (by decide),
      Nat.totient_prime_pow (by decide : Nat.Prime 3) (by decide)]
    decide
  have h3p := hc3.trans ((ArithmeticFunction.carmichael_dvd h9).trans hc)
  omega

/-- **Fermat-type characterizations of Sophie Germain primes.** Let $p$ be a prime. Then $p$ is a
Sophie Germain prime if and only if $a^{2p} \equiv (2p + 1)\,a^{p+1} - 2p \pmod{p(2p + 1)}$ for
every integer $a$ coprime to $p(2p + 1)$; and $p$ is a Sophie Germain prime if and only if
$(2p + 1)\,a^{p-1} \equiv p\,a^{2p} + p + 1 \pmod{p(2p + 1)}$ for every integer $a$ coprime to
$p(2p + 1)$.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.3, Congruences (3.5) (`integers-2025-A31-thm-3-3`). -/
public theorem isSophieGermainPrime_iff_forall_fermat_congruence {p : ℕ}
    (hp : p.Prime) :
    (Nat.IsSophieGermainPrime p ↔ ∀ a : ℤ, IsCoprime a ((p : ℤ) * (2 * p + 1)) →
        a ^ (2 * p) ≡ (2 * p + 1) * a ^ (p + 1) - 2 * p [ZMOD (p : ℤ) * (2 * p + 1)]) ∧
      (Nat.IsSophieGermainPrime p ↔ ∀ a : ℤ, IsCoprime a ((p : ℤ) * (2 * p + 1)) →
        (2 * p + 1) * a ^ (p - 1) ≡ p * a ^ (2 * p) + p + 1 [ZMOD (p : ℤ) * (2 * p + 1)]) := by
  let m := 2 * p + 1
  have hpLe := hp.two_le
  have hmcast : (m : ℤ) = 2 * (p : ℤ) + 1 := by simp [m]
  have hpm : p.Coprime m := (Nat.coprime_mul_right_add_right p 1 2).mpr (Nat.coprime_one_right p)
  have hcrt {x y : ℤ} : (x ≡ y [ZMOD p]) ∧ (x ≡ y [ZMOD m]) ↔ x ≡ y [ZMOD (p : ℤ) * m] :=
    Int.modEq_and_modEq_iff_modEq_mul (by simpa using hpm)
  have hpoint (a : ℤ) (ha : IsCoprime a ((p : ℤ) * m)) :
      (a ^ (2 * p) ≡ (m : ℤ) * a ^ (p + 1) - 2 * p [ZMOD (p : ℤ) * m] ↔
        a ^ (2 * p) ≡ 1 [ZMOD m]) ∧
      ((m : ℤ) * a ^ (p - 1) ≡ p * a ^ (2 * p) + p + 1 [ZMOD (p : ℤ) * m] ↔
        a ^ (2 * p) ≡ 1 [ZMOD m]) := by
    have hF := Int.ModEq.pow_card_sub_one_eq_one hp ha.of_mul_right_left
    have hFp : (a : ZMod p) ^ (p - 1) = 1 := by
      simpa using (ZMod.intCast_eq_intCast_iff _ _ p).mpr hF
    have h₁ : a ^ (2 * p) ≡ (m : ℤ) * a ^ (p + 1) - 2 * p [ZMOD p] := by
      rw [hmcast, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [ZMod.natCast_self, show 2 * p = (p - 1) + (p + 1) by omega, pow_add, hFp]
      simp
    have h₂ : (m : ℤ) * a ^ (p - 1) ≡ p * a ^ (2 * p) + p + 1 [ZMOD p] := by
      rw [hmcast, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      simp [hFp]
    have hm0 : 2 * (p : ZMod m) + 1 = 0 := by
      have h := ZMod.natCast_self m
      change ((2 * p + 1 : ℕ) : ZMod m) = 0 at h
      push_cast at h
      exact h
    have hNeg : -(2 * (p : ZMod m)) = 1 := by linear_combination -hm0
    constructor
    · rw [← hcrt, and_iff_right h₁, ← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      simp only [ZMod.natCast_self, zero_mul, zero_sub, hNeg]
    · rw [← hcrt, and_iff_right h₂, ← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      have hu : IsUnit (p : ZMod m) := (ZMod.isUnit_iff_coprime p m).mpr hpm
      rw [ZMod.natCast_self, zero_mul,
        ← hu.mul_right_inj (b := (a : ZMod m) ^ (2 * p)) (c := 1), mul_one]
      constructor <;> intro h <;> linear_combination -h - hm0
  have hprime : Nat.IsSophieGermainPrime p ↔ ∀ a : ℤ, IsCoprime a ((p : ℤ) * m) →
      a ^ (2 * p) ≡ 1 [ZMOD m] := by
    rw [Nat.isSophieGermainPrime_iff, and_iff_right hp]
    refine (prime_two_mul_add_one_iff_fermat hp).trans ⟨?_, ?_⟩
    · exact fun h a ha ↦ h a ha.of_mul_right_right
    · intro h a ha
      -- Lift `a` modulo `m` to `b` congruent to `1` modulo `p`.
      let b := a + (m : ℤ) * (1 - a)
      have hb : b = 1 + (p : ℤ) * (2 * (1 - a)) := by
        dsimp [b]
        rw [hmcast]
        ring
      have hbP : IsCoprime b (p : ℤ) := hb ▸ isCoprime_one_left.add_mul_left_left _
      have hab : a ≡ b [ZMOD m] := Int.modEq_iff_dvd.mpr ⟨1 - a, by dsimp [b]; ring⟩
      exact (hab.pow _).trans (h b (hbP.mul_right (ha.add_mul_left_left _)))
  rw [← hmcast]
  exact ⟨hprime.trans (forall_congr' fun a ↦ imp_congr_right fun ha ↦ (hpoint a ha).1.symm),
    hprime.trans (forall_congr' fun a ↦ imp_congr_right fun ha ↦ (hpoint a ha).2.symm)⟩

end MetaMathlibExt
