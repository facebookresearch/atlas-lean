/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import MathlibExt.NumberTheory.GaussianIntPrimeBasics

/-!
# Classification of the Gaussian primes

Every prime of the Gaussian integers `ℤ[i]` is associated to one of three
kinds: a rational prime `p ≡ 3 (mod 4)`, a factor `a + bi` (or its conjugate
`a - bi`) of a rational prime `p ≡ 1 (mod 4)` with `a ^ 2 + b ^ 2 = p`, or
`1 + i`. As a companion, a prime `p ≡ 1 (mod 4)` splits in the explicit form
`a + bi`, `a - bi` with `a ^ 2 + b ^ 2 = p`, both factors prime.

Source: `v1/Atlas/AlgebraNotes`, `Factorization.lean`,
`gaussian_primes_classification`. The first component of the v1 conjunction
(rational primes `≡ 3 mod 4` stay prime) is Mathlib's
`GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime` and is not restated;
the remaining components are proved here, with the primality of the split
factors routed through `GaussianInt.gaussianInt_prime_of_natAbs_norm_prime`
instead of the v1 helper.
-/

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

@[expose] public section

/-- The norm of `⟨a, b⟩` and of its conjugate `⟨a, -b⟩` in `ℤ[i]`, when
`a ^ 2 + b ^ 2 = p`. -/
private theorem norm_natAbs_mk_of_sq_add_sq {a b p : ℕ} (hab : a ^ 2 + b ^ 2 = p) :
    (Zsqrtd.norm (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)).natAbs = p ∧
      (Zsqrtd.norm (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt)).natAbs = p := by
  constructor
  · simp [Zsqrtd.norm]
    rw [show (a : ℤ) * a + (b : ℤ) * b = ↑(a ^ 2 + b ^ 2) by push_cast; ring]
    rw [hab]
    simp
  · simp [Zsqrtd.norm]
    rw [show (a : ℤ) * a + (b : ℤ) * b = ↑(a ^ 2 + b ^ 2) by push_cast; ring]
    rw [hab]
    simp

/-- Both `⟨a, b⟩` and `⟨a, -b⟩` are prime in `ℤ[i]` when `a ^ 2 + b ^ 2`
is a (rational) prime. -/
private theorem prime_mk_of_sq_add_sq {a b p : ℕ} (hp : p.Prime)
    (hab : a ^ 2 + b ^ 2 = p) :
    Prime (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∧
      Prime (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt) := by
  obtain ⟨hpos, hneg⟩ := norm_natAbs_mk_of_sq_add_sq hab
  exact ⟨gaussianInt_prime_of_natAbs_norm_prime (by rw [hpos]; exact hp),
    gaussianInt_prime_of_natAbs_norm_prime (by rw [hneg]; exact hp)⟩

/-- A prime `p ≡ 1 (mod 4)` splits in `ℤ[i]` in the explicit form
`a + bi`, `a - bi` with `a ^ 2 + b ^ 2 = p`, both factors prime.
This is the `a, b` form of `GaussianInt.gaussianInt_split_prime`. -/
public theorem gaussianInt_split_prime_sq_add_sq {p : ℕ} [Fact p.Prime]
    (h : p % 4 = 1) :
    ∃ a b : ℕ, a ^ 2 + b ^ 2 = p ∧ Prime (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∧
      Prime (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt) := by
  have hp4 : p % 4 ≠ 3 := by omega
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hp4
  obtain ⟨hpos, hneg⟩ := prime_mk_of_sq_add_sq Fact.out hab
  exact ⟨a, b, hab, hpos, hneg⟩

/-- A rational prime `p ≠ 2` with `p % 4 ≠ 3` satisfies `p % 4 = 1`:
the residues `0` and `2` mod `4` are impossible for an odd prime. -/
private theorem mod_four_eq_one_of_prime_of_ne_two {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hp3 : p % 4 ≠ 3) : p % 4 = 1 := by
  have h4 : p % 4 < 4 := Nat.mod_lt _ (by omega)
  have h0 : p % 4 ≠ 0 := by
    intro h
    have h4dvd : 4 ∣ p := Nat.dvd_of_mod_eq_zero h
    have h2dvd : 2 ∣ p := Nat.dvd_trans (by norm_num : (2 : ℕ) ∣ 4) h4dvd
    have := hp.eq_one_or_self_of_dvd 2 h2dvd
    omega
  have h2m : p % 4 ≠ 2 := by
    intro h
    have h2dvd : 2 ∣ p := by omega
    have := hp.eq_one_or_self_of_dvd 2 h2dvd
    omega
  omega

/-- **Classification of the Gaussian primes.** Every prime of `ℤ[i]` is
associated to a rational prime `p ≡ 3 (mod 4)`, to a factor `a + bi` or
`a - bi` of a rational prime `p ≡ 1 (mod 4)` with `a ^ 2 + b ^ 2 = p`,
or to `1 + i`. -/
public theorem gaussianInt_prime_associated (z : GaussianInt) (hz : Prime z) :
    (∃ p : ℕ, p.Prime ∧ p % 4 = 3 ∧ Associated z (p : GaussianInt)) ∨
      (∃ a b p : ℕ, p.Prime ∧ p % 4 = 1 ∧ a ^ 2 + b ^ 2 = p ∧
        (Associated z (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∨
          Associated z (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt))) ∨
      Associated z (⟨1, 1⟩ : GaussianInt) := by
  have hzu : ¬IsUnit z := hz.not_isUnit
  have hne0 : z ≠ 0 := hz.ne_zero
  have hnorm_ne1 : (Zsqrtd.norm z).natAbs ≠ 1 :=
    fun h => hzu (Zsqrtd.norm_eq_one_iff.mp h)
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hnorm_ne1
  have hpdvd_int : (p : ℤ) ∣ Zsqrtd.norm z := by
    have h := Int.natCast_dvd_natCast.mpr hpdvd
    rwa [Int.natAbs_of_nonneg (GaussianInt.norm_nonneg z)] at h
  have heq : z * star z = (↑(Zsqrtd.norm z) : GaussianInt) := by
    ext
    · simp [Zsqrtd.norm]
    · simp; ring
  by_cases hp3 : p % 4 = 3
  · left
    have hpG : Prime (↑p : GaussianInt) :=
      (@GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime p ⟨hp⟩).mpr hp3
    have hdvd_prod : (↑p : GaussianInt) ∣ z * star z := by
      rw [heq]
      exact_mod_cast hpdvd_int
    rcases hpG.dvd_or_dvd hdvd_prod with h1 | h2
    · exact ⟨p, hp, hp3, (hpG.irreducible.associated_of_dvd hz.irreducible h1).symm⟩
    · have h1 : (↑p : GaussianInt) ∣ z := by
        have h3 := map_dvd (starRingEnd GaussianInt) h2
        change star (↑p : GaussianInt) ∣ star (star z) at h3
        rw [star_star] at h3
        have hsp : star (↑p : GaussianInt) = ↑p := by ext <;> simp
        rwa [hsp] at h3
      exact ⟨p, hp, hp3, (hpG.irreducible.associated_of_dvd hz.irreducible h1).symm⟩
  · obtain ⟨a, b, hab⟩ := @Nat.Prime.sq_add_sq p ⟨hp⟩ hp3
    obtain ⟨hπ, hπ_neg⟩ := prime_mk_of_sq_add_sq hp hab
    have hfactor : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) * ⟨(a : ℤ), -(b : ℤ)⟩ = ↑(p : ℤ) := by
      ext
      · simp; nlinarith
      · simp; ring
    have hdvd_prod : (↑(p : ℤ) : GaussianInt) ∣ z * star z := by
      rw [heq]
      exact_mod_cast hpdvd_int
    have hdvd3 : (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∣ z * star z :=
      dvd_trans (dvd_mul_right _ _) (hfactor ▸ hdvd_prod)
    have hab_of_p2 (hp2 : p = 2) : a = 1 ∧ b = 1 := by
      subst hp2
      have ha : a ≤ 1 := by nlinarith [sq_nonneg b]
      have hb : b ≤ 1 := by nlinarith [sq_nonneg a]
      have ha0 : a ≠ 0 := by
        intro h
        subst h
        simp at hab
        nlinarith [sq_nonneg b]
      have hb0 : b ≠ 0 := by
        intro h
        subst h
        simp at hab
        nlinarith [sq_nonneg a]
      exact ⟨by omega, by omega⟩
    rcases hπ.dvd_or_dvd hdvd3 with h1 | h2
    · have hassoc := (hπ.irreducible.associated_of_dvd hz.irreducible h1).symm
      by_cases hp2 : p = 2
      · right; right
        obtain ⟨ha1, hb1⟩ := hab_of_p2 hp2
        rw [ha1, hb1] at hassoc
        simpa using hassoc
      · right; left
        exact ⟨a, b, p, hp, mod_four_eq_one_of_prime_of_ne_two hp hp2 hp3, hab,
          Or.inl hassoc⟩
    · have h3 : (⟨(a : ℤ), -(b : ℤ)⟩ : GaussianInt) ∣ z := by
        have h3 := map_dvd (starRingEnd GaussianInt) h2
        change star (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ∣ star (star z) at h3
        rw [star_star] at h3
        have hstar : star (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) = ⟨(a : ℤ), -(b : ℤ)⟩ := by
          ext <;> simp
        rwa [hstar] at h3
      have hassoc := (hπ_neg.irreducible.associated_of_dvd hz.irreducible h3).symm
      by_cases hp2 : p = 2
      · right; right
        obtain ⟨ha1, hb1⟩ := hab_of_p2 hp2
        rw [ha1, hb1] at hassoc
        exact hassoc.trans
          ⟨⟨⟨0, 1⟩, ⟨0, -1⟩, by decide, by decide⟩, by decide⟩
      · right; left
        exact ⟨a, b, p, hp, mod_four_eq_one_of_prime_of_ne_two hp hp2 hp3, hab,
          Or.inr hassoc⟩

end

end GaussianInt
