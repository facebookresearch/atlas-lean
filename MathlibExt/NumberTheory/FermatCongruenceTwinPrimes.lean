/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Int.ModEq
public import Mathlib.RingTheory.Coprime.Basic
public import MathlibExt.NumberTheory.CarmichaelNumber
import Mathlib.Data.ZMod.Units
import Mathlib.FieldTheory.Finite.Basic

/-!
# Fermat-type characterizations of twin primes

For odd `n ≥ 3`, each of the two congruences modulo `n * (n + 2)` reduces to the Fermat
congruences modulo `n` and `n + 2`. A modulus with the Fermat property is prime or Carmichael.

## References

* Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31, pp. 1–10,
  Theorem 3.1 and congruences (3.2).
* A. Korselt, *Problème chinois*, L'Intermédiaire des Mathématiciens 6 (1899), pp. 142–143
  (Korselt's criterion, cited in Agoh's §1).
-/

namespace MetaMathlibExt

private lemma prime_of_units_pow_sub_one {m : ℕ} (hm : 1 < m) (hodd : Odd m)
    (hnc : ¬Nat.IsCarmichaelNumber m) (hpow : ∀ u : (ZMod m)ˣ, u ^ (m - 1) = 1) :
    m.Prime := by
  have hexp : ArithmeticFunction.carmichael m ∣ m - 1 := by
    rw [ArithmeticFunction.carmichael_eq_exponent (by omega : m ≠ 0)]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  by_contra hnp
  apply hnc ((Nat.isCarmichaelNumber_iff_korselt m hm).mpr ⟨?_, ?_, hnp⟩)
  · -- A repeated odd prime divisor would divide both `m` and `m - 1`.
    refine Nat.squarefree_iff_prime_squarefree.mpr fun p hp hpp ↦ ?_
    have hpm : p ∣ m := (dvd_mul_right p p).trans hpp
    have hp2 : p ≠ 2 := fun he ↦ hodd.not_two_dvd_nat (he ▸ hpm)
    have hpDiv : p ∣ ArithmeticFunction.carmichael (p ^ 2) := by
      rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two 2 hp hp2,
        Nat.totient_prime_pow_succ hp 1, pow_one]
      exact dvd_mul_right _ _
    have hpPred := hpDiv.trans ((ArithmeticFunction.carmichael_dvd (pow_two p ▸ hpp)).trans hexp)
    have hdiff := Nat.dvd_sub hpm hpPred
    exact hp.not_dvd_one (by simpa only [Nat.sub_sub_self (by omega : 1 ≤ m)] using hdiff)
  · intro p hp hpm
    rw [← ArithmeticFunction.carmichael_of_prime hp]
    exact (ArithmeticFunction.carmichael_dvd hpm).trans hexp

private lemma units_pow_eq_one_of_forall_modEq {m M k : ℕ} [NeZero M] (hd : m ∣ M)
    (h : ∀ a : ℤ, IsCoprime a (M : ℤ) → a ^ k ≡ 1 [ZMOD m])
    (u : (ZMod m)ˣ) : u ^ k = 1 := by
  obtain ⟨v, rfl⟩ := ZMod.unitsMap_surjective hd u
  let a : ℤ := (v : ZMod M).val
  have ha : (a : ZMod M) = v := by simp [a]
  have hcop : IsCoprime a (M : ℤ) :=
    ((ZMod.isUnit_intCast_iff_isCoprime a M).mp (ha ▸ v.isUnit)).symm
  have hcast : (a : ZMod m) = (ZMod.unitsMap hd v : ZMod m) := by
    rw [ZMod.unitsMap_val, ← ZMod.castHom_apply (h := hd), ← ha, map_intCast]
  apply Units.ext
  rw [Units.val_pow_eq_pow_val, Units.val_one, ← hcast]
  simpa only [Int.cast_pow, Int.cast_one] using
    (ZMod.intCast_eq_intCast_iff _ _ m).mpr (h a hcop)

private lemma twin_fermat_congruences_iff {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    (hodd' : Odd (n + 2)) {a : ℤ} (ha : IsCoprime a ((n : ℤ) * (n + 2))) :
    ((2 * a ^ (n + 1) ≡ (n + 2) * a ^ 2 - n [ZMOD (n : ℤ) * (n + 2)]) ↔
      (a ^ (n - 1) ≡ 1 [ZMOD n]) ∧ (a ^ (n + 1) ≡ 1 [ZMOD ((n + 2 : ℕ) : ℤ)])) ∧
    ((n * a ^ (n + 1) ≡ (n + 2) * a ^ (n - 1) - 2 [ZMOD (n : ℤ) * (n + 2)]) ↔
      (a ^ (n - 1) ≡ 1 [ZMOD n]) ∧ (a ^ (n + 1) ≡ 1 [ZMOD ((n + 2 : ℕ) : ℤ)])) := by
  have hcop : n.Coprime (n + 2) := Nat.coprime_self_add_right.mpr hodd.coprime_two_right
  have hcrt {x y : ℤ} :
      (x ≡ y [ZMOD n]) ∧ (x ≡ y [ZMOD ((n + 2 : ℕ) : ℤ)]) ↔
        x ≡ y [ZMOD (n : ℤ) * (n + 2)] := by
    simpa only [Int.natAbs_natCast, Nat.cast_add, Nat.cast_ofNat] using
      (Int.modEq_and_modEq_iff_modEq_mul (m := (n : ℤ)) (n := ((n + 2 : ℕ) : ℤ))
        (a := x) (b := y) (by simpa only [Int.natAbs_natCast] using hcop))
  have htwo : IsUnit (2 : ZMod n) := (ZMod.isUnit_iff_coprime 2 n).mpr hodd.coprime_two_left
  have htwo' : IsUnit (2 : ZMod (n + 2)) :=
    (ZMod.isUnit_iff_coprime 2 (n + 2)).mpr hodd'.coprime_two_left
  have hu : IsUnit (a : ZMod n) :=
    (ZMod.isUnit_intCast_iff_isCoprime a n).mpr ha.of_mul_right_left.symm
  have hsum : (n : ZMod (n + 2)) + 2 = 0 := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using ZMod.natCast_self (n + 2)
  have hneg : (n : ZMod (n + 2)) = -2 := eq_neg_of_add_eq_zero_left hsum
  constructor
  · rw [← hcrt]
    refine and_congr ?_ ?_
    · rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [ZMod.natCast_self, zero_add, sub_zero, htwo.mul_right_inj,
        show n + 1 = (n - 1) + 2 by omega, pow_add,
        ← (hu.pow 2).mul_left_inj (c := 1), one_mul]
    · rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [hsum, zero_mul, zero_sub, hneg, neg_neg,
        ← htwo'.mul_right_inj (c := 1), mul_one]
  · rw [← hcrt]
    refine and_congr ?_ ?_
    · rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [ZMod.natCast_self, zero_mul, zero_add, eq_comm, sub_eq_zero,
        ← htwo.mul_right_inj (c := 1), mul_one]
    · rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
      push_cast
      rw [hsum, zero_mul, zero_sub, hneg, neg_mul, neg_inj,
        ← htwo'.mul_right_inj (c := 1), mul_one]

/-- **Fermat-type characterizations of twin primes.** Let $n \ge 3$ be odd, and suppose neither $n$
nor $n + 2$ is a Carmichael number. Then $n$ and $n + 2$ are both prime if and only if
$2a^{n+1} \equiv (n + 2)\,a^2 - n \pmod{n(n + 2)}$ for every integer $a$ coprime to $n(n + 2)$;
and $n$ and $n + 2$ are both prime if and only if
$n\,a^{n+1} \equiv (n + 2)\,a^{n-1} - 2 \pmod{n(n + 2)}$ for every integer $a$ coprime to
$n(n + 2)$.

Source: Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025), Article A31,
Theorem 3.1, Congruences (3.2) (`integers-2025-A31-thm-3-1`). -/
public theorem twinPrime_iff_forall_fermat_congruence {n : ℕ} (hodd : Odd n)
    (hn : 3 ≤ n) (hnc : ¬Nat.IsCarmichaelNumber n) (hn2c : ¬Nat.IsCarmichaelNumber (n + 2)) :
    ((n.Prime ∧ (n + 2).Prime) ↔ ∀ a : ℤ, IsCoprime a ((n : ℤ) * (n + 2)) →
        2 * a ^ (n + 1) ≡ (n + 2) * a ^ 2 - n [ZMOD (n : ℤ) * (n + 2)]) ∧
      ((n.Prime ∧ (n + 2).Prime) ↔ ∀ a : ℤ, IsCoprime a ((n : ℤ) * (n + 2)) →
        n * a ^ (n + 1) ≡ (n + 2) * a ^ (n - 1) - 2 [ZMOD (n : ℤ) * (n + 2)]) := by
  have hodd' : Odd (n + 2) := hodd.add_even (by decide)
  have hFermat : (n.Prime ∧ (n + 2).Prime) ↔
      ∀ a : ℤ, IsCoprime a ((n : ℤ) * (n + 2)) →
        (a ^ (n - 1) ≡ 1 [ZMOD n]) ∧ (a ^ (n + 1) ≡ 1 [ZMOD ((n + 2 : ℕ) : ℤ)]) := by
    constructor
    · rintro ⟨hp, hp'⟩ a ha
      exact ⟨Int.ModEq.pow_card_sub_one_eq_one hp ha.of_mul_right_left,
        Int.ModEq.pow_card_sub_one_eq_one hp' (by push_cast; exact ha.of_mul_right_right)⟩
    · intro h
      let : NeZero (n * (n + 2)) := ⟨Nat.mul_ne_zero (by omega) (by omega)⟩
      have hcop {a : ℤ} (ha : IsCoprime a ((n * (n + 2) : ℕ) : ℤ)) :
          IsCoprime a ((n : ℤ) * (n + 2)) := by push_cast at ha; exact ha
      exact ⟨prime_of_units_pow_sub_one (by omega) hodd hnc
          (units_pow_eq_one_of_forall_modEq (dvd_mul_right n (n + 2)) fun a ha ↦ (h a (hcop ha)).1),
        prime_of_units_pow_sub_one (by omega) hodd' hn2c
          (units_pow_eq_one_of_forall_modEq (dvd_mul_left (n + 2) n) fun a ha ↦ (h a (hcop ha)).2)⟩
  refine ⟨hFermat.trans ⟨?_, ?_⟩, hFermat.trans ⟨?_, ?_⟩⟩
  · exact fun h a ha ↦ (twin_fermat_congruences_iff hn hodd hodd' ha).1.mpr (h a ha)
  · exact fun h a ha ↦ (twin_fermat_congruences_iff hn hodd hodd' ha).1.mp (h a ha)
  · exact fun h a ha ↦ (twin_fermat_congruences_iff hn hodd hodd' ha).2.mpr (h a ha)
  · exact fun h a ha ↦ (twin_fermat_congruences_iff hn hodd hodd' ha).2.mp (h a ha)

end MetaMathlibExt
