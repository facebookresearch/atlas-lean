/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Ring.Periodic
public import Mathlib.RingTheory.Coprime.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Int.Basic

@[expose] public section

/-!
# Periods of multiplicative maps `ℤ →* R` and Dirichlet moduli

This module is a carrier repair of ATLAS `NumberTheoryI` Lemma 18.8: a normalized
totally multiplicative function `χ` on the integers with least positive additive
period `m` is a Dirichlet character of modulus `m'` if and only if `m ∣ m'` and
`m' ∣ m ^ k` for some `k`.

ATLAS carries `χ` as an `ArithmeticFunction ℂ`, which forces `χ 0 = 0`; period `1`
then gives `χ 1 = 0`, contradicting normalization.  Here `χ : ℤ →* R` bakes in
`χ 1 = 1` and multiplicativity without constraining `χ 0`, so the principal
modulus-`1` character is nonvacuous.

## Main definitions

* `MonoidHom.IsDirichletCharacterModulus`: `χ` is `q`-periodic and vanishes exactly
  off the integers coprime to `q`.

## Main statements

* `MonoidHom.isDirichletCharacterModulus_iff`: the modulus characterization above.
* `MonoidHom.isDirichletCharacterModulus_self`: `χ` has modulus `m` itself.
-/

namespace MonoidHom

variable {R : Type*} [MonoidWithZero R]

/-- **Dirichlet character of a given modulus.** Let $R$ be a monoid with zero, let
$\chi \colon \mathbb{Z} \to R$ be a multiplicative map with $\chi(1) = 1$, and let $q$ be a
natural number. Then $\chi$ is a Dirichlet character of modulus $q$ if $\chi(n + q) = \chi(n)$
for every integer $n$, and, for every integer $n$, $\chi(n) \neq 0$ if and only if $q$ and $n$
are coprime. -/
def IsDirichletCharacterModulus (χ : ℤ →* R) (q : ℕ) : Prop :=
  Function.Periodic χ (q : ℤ) ∧ ∀ n : ℤ, χ n ≠ 0 ↔ IsCoprime (q : ℤ) n

/-- `χ (-1)` is nonzero since its square is `χ 1 = 1`. -/
private theorem chi_neg_one_ne_zero {χ : ℤ →* R} [Nontrivial R] :
    χ (-1) ≠ 0 := by
  have hsq : χ (-1) * χ (-1) = 1 := by
    rw [← map_mul, show (-1 : ℤ) * -1 = 1 by norm_num, map_one]
  intro hz
  rw [hz, zero_mul] at hsq
  exact one_ne_zero hsq.symm

/-- Nonvanishing of `χ` depends only on `n.natAbs`, via `n = ±↑n.natAbs`. -/
private theorem chi_natAbs_ne_zero_iff {χ : ℤ →* R} [Nontrivial R]
    [IsCancelMulZero R] (n : ℤ) :
    χ n ≠ 0 ↔ χ ((n.natAbs : ℕ) : ℤ) ≠ 0 := by
  set N : ℕ := n.natAbs with hN
  rcases Int.natAbs_eq n with h | h
  · rw [h]
  · have hmap : χ (-((N : ℕ) : ℤ)) = χ (-1) * χ ((N : ℕ) : ℤ) := by
      rw [show (-((N : ℕ) : ℤ)) = (-1) * ((N : ℕ) : ℤ) by ring, map_mul]
    rw [h, hmap]
    exact ⟨fun hne h0 => hne (by rw [h0, mul_zero]),
      fun hne => mul_ne_zero chi_neg_one_ne_zero hne⟩

/-- Coprimality with `(m : ℤ)` depends only on `n.natAbs`. -/
private theorem isCoprime_natAbs_iff (m : ℕ) (n : ℤ) :
    IsCoprime (m : ℤ) n ↔ Nat.Coprime m n.natAbs := by
  rw [Int.isCoprime_iff_nat_coprime, Int.natAbs_natCast]

/-- The least positive period divides every positive period (Euclidean remainder:
`d % m` inherits periodicity, so minimality forces it to vanish). -/
private theorem period_dvd_of_min {χ : ℤ →* R} {m : ℕ} (hm : 0 < m)
    (hper : Function.Periodic χ (m : ℤ))
    (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
    {d : ℕ} (hdper : Function.Periodic χ (d : ℤ)) : m ∣ d := by
  rw [Nat.dvd_iff_mod_eq_zero]
  by_contra hne
  have hmod : 0 < d % m := Nat.pos_of_ne_zero hne
  have hper_mod : Function.Periodic χ ((d % m : ℕ) : ℤ) := by
    have hsub := hdper.sub_period (hper.nsmul (d / m))
    have heq : ((d % m : ℕ) : ℤ) = (d : ℤ) - (d / m) • (m : ℤ) := by
      have hdm := Nat.div_add_mod d m
      have hcast : ((m * (d / m) + d % m : ℕ) : ℤ) = (d : ℤ) := by
        exact_mod_cast hdm
      rw [Nat.cast_add, Nat.cast_mul] at hcast
      rw [nsmul_eq_mul, mul_comm ((d / m : ℕ) : ℤ) (m : ℤ)]
      omega
    rwa [heq]
  have hle := hmin _ hmod hper_mod
  have hlt := Nat.mod_lt d hm
  omega

/-- Periodicity is inherited along divisibility of moduli. -/
private theorem periodic_of_dvd {χ : ℤ →* R} {m m' : ℕ}
    (hper : Function.Periodic χ (m : ℤ)) (h : m ∣ m') :
    Function.Periodic χ ((m' : ℕ) : ℤ) := by
  obtain ⟨t, rfl⟩ := h
  have hcast : ((m * t : ℕ) : ℤ) = (t : ℕ) * (m : ℤ) := by
    rw [Nat.cast_mul, mul_comm]
  rw [hcast]
  exact hper.nat_mul t

/-- A periodic map is constant on cosets `a + m * t`. -/
private theorem periodic_eq_of_add_mul {χ : ℤ →* R} {m : ℕ}
    (hper : Function.Periodic χ (m : ℤ)) (a t : ℤ) :
    χ (a + (m : ℤ) * t) = χ a := by
  have h := hper.zsmul t a
  rw [Int.zsmul_eq_mul, mul_comm t] at h
  exact h

/-- A periodic map agrees on `ZMOD`-congruent integers. -/
private theorem periodic_eq_of_modEq {χ : ℤ →* R} {m : ℕ}
    (hper : Function.Periodic χ (m : ℤ)) {a b : ℤ}
    (h : a ≡ b [ZMOD (m : ℤ)]) : χ a = χ b := by
  obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp h
  have hba : b = a + (m : ℤ) * t := by rw [← ht]; ring
  rw [hba]
  exact (periodic_eq_of_add_mul hper a t).symm

/-- Nonvanishing at `n` forces coprimality with `m`: a common prime divisor `p`
would give `χ p ≠ 0` (else `χ n = 0`) while `m / p` is a smaller period
(cancelling the nonzero `χ p`). -/
private theorem nonzero_imp_coprime {χ : ℤ →* R} [IsCancelMulZero R] {m : ℕ}
    (hm : 0 < m)
    (hper : Function.Periodic χ (m : ℤ))
    (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
    {n : ℤ} (hn : χ n ≠ 0) : IsCoprime (m : ℤ) n := by
  rw [isCoprime_natAbs_iff]
  by_contra hnc
  obtain ⟨p, hpprime, hpm, hpn⟩ := Nat.Prime.not_coprime_iff_dvd.mp hnc
  have hpdvd : (p : ℤ) ∣ n := Int.natCast_dvd.mpr hpn
  have hχp : χ (p : ℤ) ≠ 0 := by
    intro h0
    obtain ⟨t, ht⟩ := hpdvd
    exact hn (by rw [ht, map_mul, h0, zero_mul])
  have hdivpos : 0 < m / p := Nat.div_pos (Nat.le_of_dvd hm hpm) hpprime.pos
  have hdivlt : m / p < m := Nat.div_lt_self hm hpprime.one_lt
  have hperdiv : Function.Periodic χ ((m / p : ℕ) : ℤ) := by
    intro r
    have hper_r := hper (r * (p : ℤ))
    have hdecomp : r * (p : ℤ) + (m : ℤ) = (r + ((m / p : ℕ) : ℤ)) * (p : ℤ) := by
      have hcancel := Nat.div_mul_cancel hpm
      have hcast : (((m / p * p : ℕ)) : ℤ) = (m : ℤ) := by exact_mod_cast hcancel
      rw [Nat.cast_mul] at hcast
      rw [hcast.symm]
      ring
    simp only [map_mul] at hper_r
    rw [hdecomp] at hper_r
    simp only [map_mul] at hper_r
    exact mul_right_cancel₀ hχp hper_r
  have hle := hmin _ hdivpos hperdiv
  omega

/-- Coprimality with `m` forces nonvanishing: with `N = n.natAbs`, Euler gives
`N ^ φ ≡ 1 [MOD m]`, so `χ N ^ φ = χ 1 = 1`. -/
private theorem coprime_imp_nonzero {χ : ℤ →* R} [Nontrivial R]
    [IsCancelMulZero R] {m : ℕ} (hm : 0 < m)
    (hper : Function.Periodic χ (m : ℤ))
    {n : ℤ} (hcop : IsCoprime (m : ℤ) n) : χ n ≠ 0 := by
  rw [chi_natAbs_ne_zero_iff]
  have hcopN : Nat.Coprime m n.natAbs := (isCoprime_natAbs_iff m n).mp hcop
  intro h0
  have heuler : n.natAbs ^ m.totient ≡ 1 [MOD m] :=
    Nat.ModEq.pow_totient hcopN.symm
  have htot : 0 < m.totient := Nat.totient_pos.mpr hm
  have hχpow : χ ((n.natAbs ^ m.totient : ℕ) : ℤ) = χ 1 := by
    apply periodic_eq_of_modEq hper
    have hI := Int.natCast_modEq_iff.mpr heuler
    rwa [Nat.cast_one] at hI
  have h0pow : χ ((n.natAbs ^ m.totient : ℕ) : ℤ) = 0 := by
    rw [Nat.cast_pow, map_pow, h0]
    exact zero_pow (ne_of_gt htot)
  rw [map_one] at hχpow
  rw [h0pow] at hχpow
  exact one_ne_zero hχpow.symm

/-- **Moduli of a character with a given least period.** Let $R$ be a nontrivial monoid with zero
in which nonzero elements can be cancelled on both sides, and let $\chi \colon \mathbb{Z} \to R$
be a multiplicative map with $\chi(1) = 1$. Suppose $m \ge 1$ is the least positive period of
$\chi$: $\chi(n + m) = \chi(n)$ for every integer $n$, and every positive integer $d$ with
$\chi(n + d) = \chi(n)$ for all $n$ satisfies $m \le d$. Then for every integer $m' \ge 1$,
$\chi$ is a Dirichlet character of modulus $m'$ if and only if $m \mid m'$ and $m' \mid m^k$
for some natural number $k$.

The hypothesis that $R$ is nontrivial cannot be dropped: in the zero monoid every value of
$\chi$ is $0$, so $\chi$ is a Dirichlet character of no modulus.

Source: ATLAS `NumberTheoryI` Lemma 18.8. Forward: minimality gives the divisibility, and a
prime divisor of `m'` divides `m` (else `χ p` is simultaneously zero and nonzero). Backward:
periodicity lifts along `m ∣ m'`, and the nonvanishing locus transfers via the two lemmas
above. -/
theorem isDirichletCharacterModulus_iff {χ : ℤ →* R} [Nontrivial R]
    [IsCancelMulZero R] {m m' : ℕ}
    (hm : 0 < m)
    (hper : Function.Periodic χ (m : ℤ))
    (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d)
    (hm' : 0 < m') :
    χ.IsDirichletCharacterModulus m' ↔ m ∣ m' ∧ ∃ k : ℕ, m' ∣ m ^ k := by
  constructor
  · intro hchar
    obtain ⟨hper', hnonzero⟩ := hchar
    refine ⟨period_dvd_of_min hm hper hmin hper', ?_⟩
    rw [Nat.exists_dvd_pow_iff (ne_of_gt hm') (ne_of_gt hm)]
    intro p hp
    rw [Nat.mem_primeFactors] at hp ⊢
    obtain ⟨hpprime, hpdvd, -⟩ := hp
    refine ⟨hpprime, ?_, ne_of_gt hm⟩
    by_contra hdiv
    have hcop : Nat.Coprime m p := (hpprime.coprime_iff_not_dvd.mpr hdiv).symm
    have hχp : χ (p : ℤ) ≠ 0 := coprime_imp_nonzero hm hper hcop.isCoprime
    have hncop : ¬ IsCoprime ((m' : ℕ) : ℤ) ((p : ℕ) : ℤ) := by
      rw [Nat.isCoprime_iff_coprime]
      exact fun hcop' => (hpprime.coprime_iff_not_dvd.mp hcop'.symm) hpdvd
    exact hncop ((hnonzero _).mp hχp)
  · intro hchar
    obtain ⟨hdvd, k, hk⟩ := hchar
    have hper' : Function.Periodic χ ((m' : ℕ) : ℤ) := periodic_of_dvd hper hdvd
    refine ⟨hper', fun n => ?_⟩
    constructor
    · intro hne
      have hcopm := nonzero_imp_coprime hm hper hmin hne
      have hmk : IsCoprime (((m ^ k : ℕ)) : ℤ) n := by
        rw [Nat.cast_pow]
        exact hcopm.pow_left
      exact hmk.of_isCoprime_of_dvd_left (by exact_mod_cast hk)
    · intro hcop
      have hcopm : IsCoprime ((m : ℕ) : ℤ) n :=
        hcop.of_isCoprime_of_dvd_left (by exact_mod_cast hdvd)
      exact coprime_imp_nonzero hm hper hcopm

/-- **A character is a Dirichlet character modulo its least period.** Let $R$ be a nontrivial
monoid with zero in which nonzero elements can be cancelled on both sides, and let
$\chi \colon \mathbb{Z} \to R$ be a multiplicative map with $\chi(1) = 1$. If $m \ge 1$ is the
least positive period of $\chi$ (that is, $\chi(n + m) = \chi(n)$ for every integer $n$, and every
positive integer $d$ with $\chi(n + d) = \chi(n)$ for all $n$ satisfies $m \le d$), then $\chi$
is a Dirichlet character of modulus $m$. -/
theorem isDirichletCharacterModulus_self {χ : ℤ →* R} [Nontrivial R]
    [IsCancelMulZero R] {m : ℕ} (hm : 0 < m)
    (hper : Function.Periodic χ (m : ℤ))
    (hmin : ∀ d : ℕ, 0 < d → Function.Periodic χ (d : ℤ) → m ≤ d) :
    χ.IsDirichletCharacterModulus m := by
  rw [isDirichletCharacterModulus_iff hm hper hmin hm]
  exact ⟨dvd_rfl, 1, by simp⟩

end MonoidHom
