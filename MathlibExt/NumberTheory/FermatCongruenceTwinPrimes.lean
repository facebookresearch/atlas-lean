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
public import MathlibExt.NumberTheory.CarmichaelNumber
import Mathlib.Data.ZMod.Units
import Mathlib.GroupTheory.Exponent
import Mathlib.Tactic

/-!
# Fermat-type characterizations of twin primes

Theorem 3.1 of Takashi Agoh, *A Note on Fermat's Congruence*, INTEGERS 25 (2025),
Article A31. For odd `n ≥ 3` with neither `n` nor `n + 2` a Carmichael number,
`n` and `n + 2` are both prime if and only if either of the two Fermat-type
congruences in the main theorem holds for every integer coprime to `n (n + 2)`.
Both congruences are equivalent, modulo each factor, to the Fermat congruences
`a ^ (n - 1) ≡ 1 [ZMOD n]` and `a ^ (n + 1) ≡ 1 [ZMOD n + 2]`, and a number
satisfying the Fermat congruence for every coprime base is prime unless it is
a Carmichael number.
-/

namespace MetaMathlibExt

private lemma twinPrimeFermat_prime_of_fermat_of_not_carmichael {k : ℕ} (hk : 1 < k)
    (hodd : Odd k) (hnc : ¬Nat.IsCarmichaelNumber k)
    (H : ∀ a : ℤ, IsCoprime a (k : ℤ) → a ^ (k - 1) ≡ 1 [ZMOD k]) : k.Prime := by
  by_contra hnp
  apply hnc
  have hk0 : k ≠ 0 := by omega
  have hlam : ArithmeticFunction.carmichael k ∣ k - 1 := by
    rw [ArithmeticFunction.carmichael_eq_exponent hk0,
      Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro u
    obtain ⟨a, ha⟩ := ZMod.intCast_surjective (u : ZMod k)
    have hcop : IsCoprime a (k : ℤ) := by
      have hu : IsUnit (a : ZMod k) := ha ▸ (u.isUnit)
      exact ((ZMod.isUnit_intCast_iff_isCoprime a k).mp hu).symm
    have h1 := H a hcop
    rw [← ZMod.intCast_eq_intCast_iff] at h1
    push_cast at h1
    have h2 : ((u ^ (k - 1) : (ZMod k)ˣ) : ZMod k) = 1 := by
      rw [Units.val_pow_eq_pow_val, ← ha]; exact h1
    exact Units.ext h2
  have hdiv : ∀ p : ℕ, p.Prime → p ∣ k → (p - 1) ∣ (k - 1) := by
    intro p hp hpk
    rw [← ArithmeticFunction.carmichael_of_prime hp]
    exact dvd_trans (ArithmeticFunction.carmichael_dvd hpk) hlam
  have hsq : Squarefree k := by
    rw [Nat.squarefree_iff_prime_squarefree]
    intro p hp hpp
    have hpk : p ∣ k := dvd_trans (dvd_mul_right p p) hpp
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨t, ht⟩ := hodd
      omega
    have hmem : p ∈ k.primeFactors :=
      Nat.mem_primeFactors.mpr ⟨hp, hpk, hk0⟩
    have hle : 2 ≤ k.factorization p := by
      have h2dvd : p ^ 2 ∣ k := by simpa [pow_two] using hpp
      exact (hp.pow_dvd_iff_le_factorization hk0).mp h2dvd
    have hNe : NeZero k := ⟨hk0⟩
    have hdvd : ArithmeticFunction.carmichael (p ^ k.factorization p) ∣
        ArithmeticFunction.carmichael k := by
      rw [ArithmeticFunction.carmichael_factorization k]
      exact Finset.dvd_lcm hmem
    have hcar : ArithmeticFunction.carmichael (p ^ k.factorization p) =
        (p ^ k.factorization p).totient := by
      rw [ArithmeticFunction.carmichael_pow_of_prime_ne_two _ hp hp2]
    have htot : (p ^ k.factorization p).totient =
        p ^ (k.factorization p - 1) * (p - 1) :=
      Nat.totient_prime_pow hp (by omega)
    have hpdvd : p ∣ ArithmeticFunction.carmichael (p ^ k.factorization p) := by
      rw [hcar, htot]
      exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega : k.factorization p - 1 ≠ 0)) _
    have hpk1 : p ∣ k - 1 := dvd_trans (dvd_trans hpdvd hdvd) hlam
    have h1z : (p : ℤ) ∣ 1 := by
      have hk1 : (p : ℤ) ∣ (k : ℤ) := by exact_mod_cast hpk
      have hk2 : (p : ℤ) ∣ (k : ℤ) - 1 := by
        have hcast : ((k - 1 : ℕ) : ℤ) = (k : ℤ) - 1 := by
          rw [Nat.cast_sub (by omega : 1 ≤ k)]; simp
        rw [← hcast]; exact_mod_cast hpk1
      have h := dvd_sub hk1 hk2
      simpa using h
    exact hp.not_dvd_one (by exact_mod_cast h1z)
  exact (Nat.isCarmichaelNumber_iff_korselt k hk).mpr ⟨hsq, hdiv, hnp⟩

private lemma twinPrimeFermat_isUnit_two {n : ℕ} (hodd : Odd n) :
    IsUnit (2 : ZMod n) :=
  (ZMod.isUnit_iff_coprime 2 n).mpr (Nat.coprime_two_left.mpr hodd)

private lemma twinPrimeFermat_isUnit_two_add {n : ℕ} (hodd : Odd n) :
    IsUnit (2 : ZMod (n + 2)) :=
  (ZMod.isUnit_iff_coprime 2 (n + 2)).mpr (Nat.coprime_two_left.mpr
    ⟨n / 2 + 1, by obtain ⟨t, ht⟩ := hodd; omega⟩)

private lemma twinPrimeFermat_cast_add_two_eq_zero {n : ℕ} :
    ((n : ZMod (n + 2)) + 2) = 0 := by
  have h1 : ((n : ZMod (n + 2)) + 2) = ((n + 2 : ℕ) : ZMod (n + 2)) := by
    push_cast; ring
  rw [h1, ZMod.natCast_self]

private lemma twinPrimeFermat_cast_eq_neg_two {n : ℕ} :
    ((n : ZMod (n + 2))) = -2 :=
  eq_neg_of_add_eq_zero_left twinPrimeFermat_cast_add_two_eq_zero

private lemma twinPrimeFermat_one_mod_left {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) {a : ℤ}
    (ha : IsCoprime a (n : ℤ)) :
    2 * a ^ (n + 1) ≡ (n + 2) * a ^ 2 - n [ZMOD (n : ℤ)] ↔
      a ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)] := by
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_self]
  simp only [zero_add, sub_zero]
  have hA : IsUnit (a : ZMod n) := (ZMod.isUnit_intCast_iff_isCoprime a n).mpr ha.symm
  have hexp : n + 1 = (n - 1) + 2 := by omega
  rw [hexp, pow_add]
  have hU : IsUnit ((2 : ZMod n) * (a : ZMod n) ^ 2) :=
    (twinPrimeFermat_isUnit_two hodd).mul (hA.pow 2)
  rw [show (2 : ZMod n) * ((a : ZMod n) ^ (n - 1) * (a : ZMod n) ^ 2) =
      (a : ZMod n) ^ (n - 1) * ((2 : ZMod n) * (a : ZMod n) ^ 2) by ring]
  conv_lhs => rhs; rw [show (2 : ZMod n) * (a : ZMod n) ^ 2 =
      (1 : ZMod n) * ((2 : ZMod n) * (a : ZMod n) ^ 2) by ring]
  exact hU.mul_left_inj

private lemma twinPrimeFermat_one_mod_right {n : ℕ} (hodd : Odd n) {a : ℤ} :
    2 * a ^ (n + 1) ≡ (n + 2) * a ^ 2 - n [ZMOD (n : ℤ) + 2] ↔
      a ^ (n + 1) ≡ 1 [ZMOD (n : ℤ) + 2] := by
  have hmod : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  rw [← hmod]
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [twinPrimeFermat_cast_add_two_eq_zero, twinPrimeFermat_cast_eq_neg_two]
  simp only [zero_mul, sub_neg_eq_add]
  rw [show (0 : ZMod (n + 2)) + 2 = 2 * (1 : ZMod (n + 2)) by ring]
  exact (twinPrimeFermat_isUnit_two_add hodd).mul_right_inj

private lemma twinPrimeFermat_two_mod_left {n : ℕ} (hodd : Odd n) {a : ℤ} :
    (n : ℤ) * a ^ (n + 1) ≡ (n + 2) * a ^ (n - 1) - 2 [ZMOD (n : ℤ)] ↔
      a ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)] := by
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [ZMod.natCast_self]
  simp only [zero_mul, zero_add]
  have key : (0 : ZMod n) = 2 * (a : ZMod n) ^ (n - 1) - 2 ↔
      2 * (a : ZMod n) ^ (n - 1) = 2 * (1 : ZMod n) := by
    constructor
    · intro h; linear_combination -h
    · intro h; linear_combination -h
  rw [key]
  exact (twinPrimeFermat_isUnit_two hodd).mul_right_inj

private lemma twinPrimeFermat_two_mod_right {n : ℕ} (hodd : Odd n) {a : ℤ} :
    (n : ℤ) * a ^ (n + 1) ≡ (n + 2) * a ^ (n - 1) - 2 [ZMOD (n : ℤ) + 2] ↔
      a ^ (n + 1) ≡ 1 [ZMOD (n : ℤ) + 2] := by
  have hmod : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  rw [← hmod]
  rw [← ZMod.intCast_eq_intCast_iff, ← ZMod.intCast_eq_intCast_iff]
  push_cast
  rw [twinPrimeFermat_cast_add_two_eq_zero, twinPrimeFermat_cast_eq_neg_two]
  simp only [zero_mul, zero_sub]
  nth_rewrite 2 [← mul_one (-2 : ZMod (n + 2))]
  exact (twinPrimeFermat_isUnit_two_add hodd).neg.mul_right_inj

private lemma twinPrimeFermat_isCoprime {n : ℕ} (hodd : Odd n) :
    IsCoprime (n : ℤ) ((n : ℤ) + 2) := by
  obtain ⟨t, ht⟩ := hodd
  have hnZ : (n : ℤ) = 2 * t + 1 := by exact_mod_cast ht
  refine ⟨t + 1, -t, ?_⟩
  rw [hnZ]
  ring

private lemma twinPrimeFermat_coprime {n : ℕ} (hodd : Odd n) :
    Nat.Coprime n (n + 2) := by
  have hmod : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  have h : IsCoprime (n : ℤ) ((n + 2 : ℕ) : ℤ) := by
    rw [hmod]; exact twinPrimeFermat_isCoprime hodd
  exact Nat.isCoprime_iff_coprime.mp h

private lemma twinPrimeFermat_lift_left {n : ℕ} (hodd : Odd n) {a : ℤ}
    (ha : IsCoprime a (n : ℤ)) :
    ∃ b : ℤ, IsCoprime b ((n : ℤ) * ((n : ℤ) + 2)) ∧ a ≡ b [ZMOD (n : ℤ)] := by
  obtain ⟨s, t, hst⟩ := twinPrimeFermat_isCoprime hodd
  refine ⟨a + (n : ℤ) * (s - a * s), ?_, ?_⟩
  · have hb : a + (n : ℤ) * (s - a * s) =
        1 + ((n : ℤ) + 2) * (a * t - t) := by
      linear_combination (1 - a) * hst
    exact (ha.add_mul_left_left _).mul_right (hb ▸ isCoprime_one_left.add_mul_left_left _)
  · exact Int.modEq_iff_dvd.mpr ⟨s - a * s, by ring⟩

private lemma twinPrimeFermat_lift_right {n : ℕ} (hodd : Odd n) {a : ℤ}
    (ha : IsCoprime a ((n : ℤ) + 2)) :
    ∃ b : ℤ, IsCoprime b ((n : ℤ) * ((n : ℤ) + 2)) ∧ a ≡ b [ZMOD (n : ℤ) + 2] := by
  obtain ⟨s, t, hst⟩ := twinPrimeFermat_isCoprime hodd
  refine ⟨a + ((n : ℤ) + 2) * (t - a * t), ?_, ?_⟩
  · have hc : a + ((n : ℤ) + 2) * (t - a * t) =
        1 + (n : ℤ) * (a * s - s) := by
      linear_combination (1 - a) * hst
    exact (hc ▸ isCoprime_one_left.add_mul_left_left _).mul_right (ha.add_mul_left_left _)
  · exact Int.modEq_iff_dvd.mpr ⟨t - a * t, by ring⟩

private lemma twinPrimeFermat_one_pointwise {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n)
    {a : ℤ} (ha : IsCoprime a ((n : ℤ) * ((n : ℤ) + 2))) :
    (2 * a ^ (n + 1) ≡ (n + 2) * a ^ 2 - n [ZMOD (n : ℤ) * ((n : ℤ) + 2)]) ↔
      (a ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)] ∧ a ^ (n + 1) ≡ 1 [ZMOD (n : ℤ) + 2]) := by
  have hmn : ((n : ℤ)).natAbs.Coprime (((n : ℤ) + 2)).natAbs := by
    have h2 : ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [h2, Int.natAbs_natCast, Int.natAbs_natCast]
    exact twinPrimeFermat_coprime hodd
  rw [← Int.modEq_and_modEq_iff_modEq_mul hmn,
    twinPrimeFermat_one_mod_left hn hodd ha.of_mul_right_left,
    twinPrimeFermat_one_mod_right hodd]

private lemma twinPrimeFermat_two_pointwise {n : ℕ} (hodd : Odd n) {a : ℤ} :
    ((n : ℤ) * a ^ (n + 1) ≡ (n + 2) * a ^ (n - 1) - 2
        [ZMOD (n : ℤ) * ((n : ℤ) + 2)]) ↔
      (a ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)] ∧ a ^ (n + 1) ≡ 1 [ZMOD (n : ℤ) + 2]) := by
  have hmn : ((n : ℤ)).natAbs.Coprime (((n : ℤ) + 2)).natAbs := by
    have h2 : ((n : ℤ) + 2) = ((n + 2 : ℕ) : ℤ) := by push_cast; ring
    rw [h2, Int.natAbs_natCast, Int.natAbs_natCast]
    exact twinPrimeFermat_coprime hodd
  rw [← Int.modEq_and_modEq_iff_modEq_mul hmn,
    twinPrimeFermat_two_mod_left hodd, twinPrimeFermat_two_mod_right hodd]

private lemma twinPrimeFermat_forall_one_iff {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) :
    (∀ a : ℤ, IsCoprime a ((n : ℤ) * ((n : ℤ) + 2)) →
        2 * a ^ (n + 1) ≡ (n + 2) * a ^ 2 - n [ZMOD (n : ℤ) * ((n : ℤ) + 2)]) ↔
      (∀ a : ℤ, IsCoprime a (n : ℤ) → a ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)]) ∧
        (∀ a : ℤ, IsCoprime a ((n : ℤ) + 2) → a ^ (n + 1) ≡ 1 [ZMOD (n : ℤ) + 2]) := by
  constructor
  · intro H
    constructor
    · intro a ha
      obtain ⟨b, hb, hba⟩ := twinPrimeFermat_lift_left hodd ha
      exact (hba.pow (n - 1)).trans ((twinPrimeFermat_one_pointwise hn hodd hb).mp (H b hb)).1
    · intro a ha
      obtain ⟨b, hb, hba⟩ := twinPrimeFermat_lift_right hodd ha
      exact (hba.pow (n + 1)).trans ((twinPrimeFermat_one_pointwise hn hodd hb).mp (H b hb)).2
  · rintro ⟨Hn, Hm⟩ a ha
    exact (twinPrimeFermat_one_pointwise hn hodd ha).mpr
      ⟨Hn a ha.of_mul_right_left, Hm a ha.of_mul_right_right⟩

private lemma twinPrimeFermat_forall_two_iff {n : ℕ} (hodd : Odd n) :
    (∀ a : ℤ, IsCoprime a ((n : ℤ) * ((n : ℤ) + 2)) →
        (n : ℤ) * a ^ (n + 1) ≡ (n + 2) * a ^ (n - 1) - 2
          [ZMOD (n : ℤ) * ((n : ℤ) + 2)]) ↔
      (∀ a : ℤ, IsCoprime a (n : ℤ) → a ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)]) ∧
        (∀ a : ℤ, IsCoprime a ((n : ℤ) + 2) → a ^ (n + 1) ≡ 1 [ZMOD (n : ℤ) + 2]) := by
  constructor
  · intro H
    constructor
    · intro a ha
      obtain ⟨b, hb, hba⟩ := twinPrimeFermat_lift_left hodd ha
      exact (hba.pow (n - 1)).trans ((twinPrimeFermat_two_pointwise hodd).mp (H b hb)).1
    · intro a ha
      obtain ⟨b, hb, hba⟩ := twinPrimeFermat_lift_right hodd ha
      exact (hba.pow (n + 1)).trans ((twinPrimeFermat_two_pointwise hodd).mp (H b hb)).2
  · rintro ⟨Hn, Hm⟩ a ha
    exact (twinPrimeFermat_two_pointwise hodd).mpr
      ⟨Hn a ha.of_mul_right_left, Hm a ha.of_mul_right_right⟩

private lemma twinPrimeFermat_prime_add_two_of_fermat {n : ℕ} (hodd : Odd n)
    (hn2c : ¬Nat.IsCarmichaelNumber (n + 2))
    (Hm : ∀ a : ℤ, IsCoprime a ((n : ℤ) + 2) →
      a ^ (n + 1) ≡ 1 [ZMOD (n : ℤ) + 2]) : (n + 2).Prime := by
  have hmod : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  have hodd2 : Odd (n + 2) := by
    obtain ⟨t, ht⟩ := hodd
    exact ⟨t + 1, by omega⟩
  apply twinPrimeFermat_prime_of_fermat_of_not_carmichael (by omega) hodd2 hn2c
  intro a ha
  have ha2 : IsCoprime a ((n : ℤ) + 2) := by rwa [hmod] at ha
  have h := Hm a ha2
  rw [hmod]
  have hexp : n + 2 - 1 = n + 1 := by omega
  rwa [hexp]

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
  have hmod : ((n + 2 : ℕ) : ℤ) = (n : ℤ) + 2 := by push_cast; ring
  have hfermat_of_prime : n.Prime → (n + 2).Prime →
      (∀ a : ℤ, IsCoprime a (n : ℤ) → a ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)]) ∧
        (∀ a : ℤ, IsCoprime a ((n : ℤ) + 2) → a ^ (n + 1) ≡ 1 [ZMOD (n : ℤ) + 2]) := by
    intro hp hp2
    refine ⟨fun a ha ↦ Int.ModEq.pow_card_sub_one_eq_one hp ha, fun a ha ↦ ?_⟩
    have ha' : IsCoprime a ((n + 2 : ℕ) : ℤ) := by rw [hmod]; exact ha
    have h := Int.ModEq.pow_card_sub_one_eq_one hp2 ha'
    rw [hmod] at h
    have hexp : n + 2 - 1 = n + 1 := by omega
    rwa [hexp] at h
  have hprime_of_fermat :
      (∀ a : ℤ, IsCoprime a (n : ℤ) → a ^ (n - 1) ≡ 1 [ZMOD (n : ℤ)]) →
        (∀ a : ℤ, IsCoprime a ((n : ℤ) + 2) → a ^ (n + 1) ≡ 1 [ZMOD (n : ℤ) + 2]) →
          n.Prime ∧ (n + 2).Prime :=
    fun Hn Hm ↦ ⟨twinPrimeFermat_prime_of_fermat_of_not_carmichael (by omega) hodd hnc Hn,
      twinPrimeFermat_prime_add_two_of_fermat hodd hn2c Hm⟩
  constructor
  · constructor
    · intro hprimes
      exact (twinPrimeFermat_forall_one_iff hn hodd).mpr
        (hfermat_of_prime hprimes.1 hprimes.2)
    · intro H
      obtain ⟨Hn, Hm⟩ := (twinPrimeFermat_forall_one_iff hn hodd).mp H
      exact hprime_of_fermat Hn Hm
  · constructor
    · intro hprimes
      exact (twinPrimeFermat_forall_two_iff hodd).mpr
        (hfermat_of_prime hprimes.1 hprimes.2)
    · intro H
      obtain ⟨Hn, Hm⟩ := (twinPrimeFermat_forall_two_iff hodd).mp H
      exact hprime_of_fermat Hn Hm

end MetaMathlibExt
