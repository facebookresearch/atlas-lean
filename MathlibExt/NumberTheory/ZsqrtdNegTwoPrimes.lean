/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.LegendreSymbol.QuadraticReciprocity
public import MathlibExt.NumberTheory.ZsqrtdNegTwoEuclidean
public import MathlibExt.NumberTheory.ZsqrtdNormFactorization

/-!
# Prime analysis in `ℤ[√-2]`

Units, norm-primality, the ramified prime `√-2`, Mathlib's mod-8 character `ZMod.χ₈'`,
and the inert/split behavior of rational primes in `ℤ[√-2]`.
-/

namespace Zsqrtd.NegTwo

@[expose] public section

open Zsqrtd

/-- **Units of ℤ[√−2].** An element $x$ of $\mathbb{Z}[\sqrt{-2}]$ is a unit if and only if $x = 1$
or $x = -1$. -/
public theorem zsqrtd_neg_two_isUnit_iff (x : ℤ√(-2 : ℤ)) :
    IsUnit x ↔ x = 1 ∨ x = -1 := by
  rw [← Zsqrtd.norm_eq_one_iff]
  constructor
  · intro h
    have hnorm : Zsqrtd.norm x = 1 := by
      have hnn := Zsqrtd.norm_nonneg (show (-2 : ℤ) ≤ 0 by norm_num) x
      have hcast : ((Zsqrtd.norm x).natAbs : ℤ) = Zsqrtd.norm x :=
        Int.natAbs_of_nonneg hnn
      omega
    cases x with
    | mk r i =>
      have h2 : r * r - -2 * i * i = 1 := hnorm
      have hsum : r * r + 2 * (i * i) = 1 := by linear_combination h2
      have hi0 : i = 0 := by
        by_contra hi
        have hpos : 0 < i * i := mul_self_pos.mpr hi
        have hnn : 0 ≤ r * r := mul_self_nonneg r
        omega
      subst hi0
      have hr1 : r * r = 1 := by linear_combination hsum
      rw [mul_self_eq_one_iff] at hr1
      rcases hr1 with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
  · rintro (rfl | rfl) <;> decide

/-- **Elements of ℤ[√−2] of prime norm are prime.** For $\pi = a + b\sqrt{-2}$ in
$\mathbb{Z}[\sqrt{-2}]$ let $N(\pi) = a^2 + 2b^2$ be its norm. If $|N(\pi)|$ is a prime number, then
$\pi$ is a prime element of $\mathbb{Z}[\sqrt{-2}]$. -/
public theorem zsqrtd_neg_two_prime_of_natAbs_norm_prime {π : ℤ√(-2 : ℤ)}
    (h : (Zsqrtd.norm π).natAbs.Prime) : Prime π :=
  Zsqrtd.prime_of_natAbs_norm_prime h

/-- **√−2 is prime in ℤ[√−2].** The element $\sqrt{-2}$ is a prime element of
$\mathbb{Z}[\sqrt{-2}]$.

Its norm is $2$, a prime number. -/
public theorem zsqrtd_neg_two_prime_sqrtd : Prime (⟨0, 1⟩ : ℤ√(-2 : ℤ)) :=
  zsqrtd_neg_two_prime_of_natAbs_norm_prime (by decide)

/-- **$2$ is minus the square of $\sqrt{-2}$.** In $\mathbb{Z}[\sqrt{-2}]$ one has
$2 = -(\sqrt{-2})^2$. -/
public theorem zsqrtd_neg_two_two_eq : (2 : ℤ√(-2 : ℤ)) = -⟨0, 1⟩ ^ 2 := by
  decide

/-- **x² + 2y² is never 5 or 7 modulo 8.** For all $x, y \in \mathbb{Z}/8\mathbb{Z}$,
$x^2 + 2y^2 \ne 5$ and $x^2 + 2y^2 \ne 7$. -/
public theorem zsqrtd_neg_two_mod8_obstruction :
    ∀ x y : ZMod 8, x ^ 2 + 2 * y ^ 2 ≠ 5 ∧ x ^ 2 + 2 * y ^ 2 ≠ 7 := by
  decide

/-- A rational prime stays nonzero in `ℤ[√-2]`. -/
private theorem ne_zero_natCast {p : ℕ} [Fact p.Prime] :
    (p : ℤ√(-2 : ℤ)) ≠ 0 := by
  intro hcon
  have hp : p.Prime := Fact.out
  have hre := congrArg Zsqrtd.re hcon
  rw [Zsqrtd.re_natCast, Zsqrtd.re_zero] at hre
  have hp0 : p = 0 := by exact_mod_cast hre
  exact hp.ne_zero hp0

/-- A rational prime is not a unit in `ℤ[√-2]`. -/
private theorem not_isUnit_natCast {p : ℕ} [Fact p.Prime] :
    ¬ IsUnit (p : ℤ√(-2 : ℤ)) := by
  intro hu
  have hp : p.Prime := Fact.out
  have h1 := Zsqrtd.norm_eq_one_iff.mpr hu
  rw [Zsqrtd.norm_natCast, Int.natAbs_mul, Int.natAbs_natCast] at h1
  have hdvd : p ∣ 1 := ⟨p, h1.symm⟩
  exact hp.ne_one (Nat.dvd_one.mp hdvd)

/-- Norms multiply to `p²` along a factorization of `p` in `ℤ[√-2]`. -/
private theorem natAbs_norm_mul {a b : ℤ√(-2 : ℤ)} {p : ℕ}
    (hab : (p : ℤ√(-2 : ℤ)) = a * b) :
    (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = p ^ 2 := by
  have h := congrArg (fun x => (Zsqrtd.norm x).natAbs) hab
  rw [Zsqrtd.norm_mul, Int.natAbs_mul, Zsqrtd.norm_natCast, Int.natAbs_mul,
    Int.natAbs_natCast, ← pow_two] at h
  exact h.symm

/-- A `natAbs`-norm of `p` lifts to a norm of `(p : ℤ)`. -/
private theorem norm_eq_natCast_of_natAbs {x : ℤ√(-2 : ℤ)} {p : ℕ}
    (h : (Zsqrtd.norm x).natAbs = p) : Zsqrtd.norm x = (p : ℤ) := by
  have hnn := Zsqrtd.norm_nonneg (show (-2 : ℤ) ≤ 0 by norm_num) x
  have h2 := Int.natAbs_of_nonneg hnn
  rw [h] at h2
  exact h2.symm

/-- A nonzero nonunit has `natAbs`-norm greater than one. -/
private theorem one_lt_natAbs_norm {x : ℤ√(-2 : ℤ)} (h0 : x ≠ 0)
    (hu : ¬ IsUnit x) : 1 < (Zsqrtd.norm x).natAbs := by
  have hne1 : (Zsqrtd.norm x).natAbs ≠ 1 :=
    fun h => hu (Zsqrtd.norm_eq_one_iff.mp h)
  have hne0 : (Zsqrtd.norm x).natAbs ≠ 0 := by
    intro h0'
    have hz : Zsqrtd.norm x = 0 := Int.natAbs_eq_zero.mp h0'
    exact h0 ((Zsqrtd.norm_eq_zero_iff (show (-2 : ℤ) < 0 by norm_num) x).mp hz)
  omega

/-- **Primes congruent to 5 or 7 mod 8 are inert in ℤ[√−2].** If $p$ is a prime number with
$p \equiv 5 \pmod 8$ or $p \equiv 7 \pmod 8$, then $p$ is a prime element of
$\mathbb{Z}[\sqrt{-2}]$. -/
public theorem zsqrtd_neg_two_inert {p : ℕ} [Fact p.Prime]
    (h : p % 8 = 5 ∨ p % 8 = 7) : Prime (p : ℤ√(-2 : ℤ)) := by
  apply UniqueFactorizationMonoid.irreducible_iff_prime.mp
  have hp : p.Prime := Fact.out
  refine ⟨not_isUnit_natCast, fun a b hab => ?_⟩
  have hnorm := natAbs_norm_mul hab
  have hdvd : (Zsqrtd.norm a).natAbs ∣ p ^ 2 := ⟨_, hnorm.symm⟩
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  interval_cases k
  · exact Or.inl (Zsqrtd.norm_eq_one_iff.mp (by simpa using hk))
  · exfalso
    have hA : (Zsqrtd.norm a).natAbs = p := by simpa using hk
    have hna := norm_eq_natCast_of_natAbs hA
    obtain ⟨x, y⟩ := a
    have h2 : x * x - -2 * y * y = (p : ℤ) := hna
    have hcast : (x : ZMod 8) ^ 2 + 2 * (y : ZMod 8) ^ 2 = (p : ZMod 8) := by
      have hcc := congrArg (fun z : ℤ => (z : ZMod 8)) h2
      push_cast at hcc
      linear_combination hcc
    have hp8 : (p : ZMod 8) = ((p % 8 : ℕ) : ZMod 8) := by
      rw [ZMod.natCast_eq_natCast_iff]
      exact (Nat.mod_modEq p 8).symm
    rcases h with h | h
    · have hp5 : (p : ZMod 8) = 5 := by
        have h5 := hp8
        rw [h] at h5
        exact_mod_cast h5
      rw [hp5] at hcast
      exact (zsqrtd_neg_two_mod8_obstruction _ _).1 hcast
    · have hp7 : (p : ZMod 8) = 7 := by
        have h7 := hp8
        rw [h] at h7
        exact_mod_cast h7
      rw [hp7] at hcast
      exact (zsqrtd_neg_two_mod8_obstruction _ _).2 hcast
  · have hA0 : (Zsqrtd.norm a).natAbs ≠ 0 := by
      rw [hk]
      exact pow_ne_zero 2 hp.ne_zero
    have hcancel : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
        = (Zsqrtd.norm a).natAbs * 1 := by
      rw [mul_one, hnorm, hk]
    exact Or.inr (Zsqrtd.norm_eq_one_iff.mp (mul_left_cancel₀ hA0 hcancel))

/-- **Primes $p \equiv 1, 3 \pmod 8$ are norms of primes of $\mathbb{Z}[\sqrt{-2}]$.**
Let $p$ be a prime number with $p \equiv 1 \pmod 8$ or $p \equiv 3 \pmod 8$. Then there is a
prime element $\pi = a + b\sqrt{-2}$ of $\mathbb{Z}[\sqrt{-2}]$ whose norm $a^2 + 2b^2$ equals
$p$. -/
public theorem zsqrtd_neg_two_split {p : ℕ} [Fact p.Prime]
    (h : p % 8 = 1 ∨ p % 8 = 3) :
    ∃ π : ℤ√(-2 : ℤ), Zsqrtd.norm π = p ∧ Prime π := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by
    rintro rfl
    rcases h with h | h <;> omega
  have hsq : IsSquare (-2 : ZMod p) := (ZMod.exists_sq_eq_neg_two_iff hp2).mpr h
  obtain ⟨r, hr⟩ := hsq
  have : NeZero p := ⟨hp.ne_zero⟩
  set a : ℤ := (r.val : ℤ) with ha
  have hrval : (a : ZMod p) = r := by
    simp only [ha, Int.cast_natCast, ZMod.natCast_zmod_val]
  have hrr : r * r + 2 = 0 := by
    have hsym := hr.symm
    linear_combination hsym
  have h0 : ((a ^ 2 + 2 : ℤ) : ZMod p) = 0 := by
    push_cast
    rw [hrval, pow_two]
    exact hrr
  have hdvd : ((p : ℕ) : ℤ) ∣ a ^ 2 + 2 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h0
  have hcast : ((p : ℕ) : ℤ√(-2 : ℤ)) = (((p : ℕ) : ℤ) : ℤ√(-2 : ℤ)) := by simp
  have hprod : (⟨a, 1⟩ : ℤ√(-2 : ℤ)) * ⟨a, -1⟩
      = ((a ^ 2 + 2 : ℤ) : ℤ√(-2 : ℤ)) := by
    refine Zsqrtd.ext ?_ ?_
    · simp only [Zsqrtd.re_mul, Zsqrtd.re_intCast]
      show a * a + -2 * 1 * -1 = a ^ 2 + 2
      ring
    · simp only [Zsqrtd.im_mul, Zsqrtd.im_intCast]
      show a * -1 + 1 * a = 0
      ring
  have hpdvd : (p : ℤ√(-2 : ℤ)) ∣ (⟨a, 1⟩ : ℤ√(-2 : ℤ)) * ⟨a, -1⟩ := by
    rw [hprod, hcast, Zsqrtd.intCast_dvd_intCast]
    exact hdvd
  have hndvd1 : ¬ (p : ℤ√(-2 : ℤ)) ∣ (⟨a, 1⟩ : ℤ√(-2 : ℤ)) := by
    intro hd
    rw [hcast, Zsqrtd.intCast_dvd] at hd
    have h1 : ((p : ℕ) : ℤ) ∣ 1 := hd.2
    have hd1 : p ∣ 1 := Int.natCast_dvd_natCast.mp h1
    exact hp.ne_one (Nat.dvd_one.mp hd1)
  have hndvd2 : ¬ (p : ℤ√(-2 : ℤ)) ∣ (⟨a, -1⟩ : ℤ√(-2 : ℤ)) := by
    intro hd
    rw [hcast, Zsqrtd.intCast_dvd] at hd
    have h1 : ((p : ℕ) : ℤ) ∣ -1 := hd.2
    have h1' : ((p : ℕ) : ℤ) ∣ 1 := dvd_neg.mp h1
    have hd1 : p ∣ 1 := Int.natCast_dvd_natCast.mp h1'
    exact hp.ne_one (Nat.dvd_one.mp hd1)
  have hnprime : ¬ Prime (p : ℤ√(-2 : ℤ)) := by
    intro hprime
    rcases hprime.dvd_mul.mp hpdvd with hh | hh
    · exact hndvd1 hh
    · exact hndvd2 hh
  have hnu : ¬ IsUnit (p : ℤ√(-2 : ℤ)) := not_isUnit_natCast
  have hne : (p : ℤ√(-2 : ℤ)) ≠ 0 := ne_zero_natCast
  have hirr : ¬ Irreducible (p : ℤ√(-2 : ℤ)) :=
    fun hi => hnprime (UniqueFactorizationMonoid.irreducible_iff_prime.mp hi)
  have hex : ∃ a b : ℤ√(-2 : ℤ),
      (p : ℤ√(-2 : ℤ)) = a * b ∧ ¬ IsUnit a ∧ ¬ IsUnit b := by
    by_contra hcon
    apply hirr
    refine ⟨hnu, fun a b hab => ?_⟩
    by_contra hcon2
    rw [not_or] at hcon2
    exact hcon ⟨a, b, hab, hcon2.1, hcon2.2⟩
  obtain ⟨α, β, hab, hα, hβ⟩ := hex
  have hα0 : α ≠ 0 := by
    rintro rfl
    rw [zero_mul] at hab
    exact hne hab
  have hβ0 : β ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hab
    exact hne hab
  have hα1 := one_lt_natAbs_norm hα0 hα
  have hβ1 := one_lt_natAbs_norm hβ0 hβ
  have hnorm := natAbs_norm_mul hab
  have hdvd2 : (Zsqrtd.norm α).natAbs ∣ p ^ 2 := ⟨_, hnorm.symm⟩
  obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow hp).mp hdvd2
  interval_cases k
  · exfalso
    have hA : (Zsqrtd.norm α).natAbs = 1 := by simpa using hk
    omega
  · have hA : (Zsqrtd.norm α).natAbs = p := by simpa using hk
    refine ⟨α, norm_eq_natCast_of_natAbs hA,
      zsqrtd_neg_two_prime_of_natAbs_norm_prime ?_⟩
    rw [hA]
    exact hp
  · exfalso
    have hA0 : (Zsqrtd.norm α).natAbs ≠ 0 := by
      rw [hk]
      exact pow_ne_zero 2 hp.ne_zero
    have hcancel : (Zsqrtd.norm α).natAbs * (Zsqrtd.norm β).natAbs
        = (Zsqrtd.norm α).natAbs * 1 := by
      rw [mul_one, hnorm, hk]
    have hB : (Zsqrtd.norm β).natAbs = 1 := mul_left_cancel₀ hA0 hcancel
    omega

/-- **Conjugate factorization of an odd prime in $\mathbb{Z}[\sqrt{-2}]$.** Let $p$ be an odd
prime number and let $\pi = a + b\sqrt{-2}$ be an element of $\mathbb{Z}[\sqrt{-2}]$ whose norm
$a^2 + 2b^2$ equals $p$. Write $\bar\pi = a - b\sqrt{-2}$ for the conjugate of $\pi$. Then
$p = \pi\bar\pi$, $\bar\pi$ is prime in $\mathbb{Z}[\sqrt{-2}]$, and $\bar\pi$ is not associated
to $\pi$. -/
public theorem zsqrtd_neg_two_split_conj {p : ℕ} [Fact p.Prime] {π : ℤ√(-2 : ℤ)}
    (hnorm : Zsqrtd.norm π = p) (hodd : p % 2 = 1) :
    (p : ℤ√(-2 : ℤ)) = π * star π ∧ Prime (star π) ∧ ¬ Associated (star π) π := by
  have hp : p.Prime := Fact.out
  have hmul : (p : ℤ√(-2 : ℤ)) = π * star π := by
    have h := Zsqrtd.norm_eq_mul_conj π
    rw [hnorm] at h
    have hcast : ((((p : ℕ) : ℤ)) : ℤ√(-2 : ℤ)) = ((p : ℕ) : ℤ√(-2 : ℤ)) := by
      simp
    rw [hcast] at h
    exact h
  have hprime : Prime (star π) := by
    apply zsqrtd_neg_two_prime_of_natAbs_norm_prime
    rw [Zsqrtd.norm_conj, hnorm, Int.natAbs_natCast]
    exact hp
  refine ⟨hmul, hprime, ?_⟩
  have hsq : ∀ c : ℤ, c * c = (p : ℤ) → False := by
    intro c hc
    have hcc : c.natAbs * c.natAbs = p := by
      have h2 := congrArg Int.natAbs hc
      rwa [Int.natAbs_mul, Int.natAbs_natCast] at h2
    have hdvd : c.natAbs ∣ p := ⟨c.natAbs, hcc.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1' | h1'
    · rw [h1', one_mul] at hcc
      exact hp.ne_one hcc.symm
    · rw [h1'] at hcc
      have hcc' : p * p = 1 * p := by rw [one_mul]; exact hcc
      have hp1 : p = 1 := mul_right_cancel₀ hp.ne_zero hcc'
      exact hp.ne_one hp1
  have h2b : ∀ c : ℤ, 2 * (c * c) = (p : ℤ) → False := by
    intro c hc
    have hcc : 2 * (c.natAbs * c.natAbs) = p := by
      have h2 := congrArg Int.natAbs hc
      simpa [Int.natAbs_mul, Int.natAbs_natCast] using h2
    have hdvd : 2 ∣ p := ⟨c.natAbs * c.natAbs, hcc.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1' | h1'
    · omega
    · omega
  intro hassoc
  obtain ⟨a, b⟩ := π
  obtain ⟨u, hu⟩ := hassoc
  have hu2 := (zsqrtd_neg_two_isUnit_iff (u : ℤ√(-2 : ℤ))).mp u.isUnit
  have hnorm2 : a * a - -2 * b * b = (p : ℤ) := by
    have h := hnorm
    rw [Zsqrtd.norm_def] at h
    exact h
  have hnorm' : a * a + 2 * (b * b) = (p : ℤ) := by linear_combination hnorm2
  rcases hu2 with hcase | hcase
  · rw [hcase, mul_one] at hu
    have him := congrArg Zsqrtd.im hu
    simp only [Zsqrtd.im_star] at him
    have hb0 : b = 0 := by
      have him' : -b = b := him
      omega
    rw [hb0] at hnorm'
    have haa : a * a = (p : ℤ) := by linear_combination hnorm'
    exact hsq a haa
  · rw [hcase] at hu
    have hre := congrArg Zsqrtd.re hu
    simp only [Zsqrtd.re_star, Zsqrtd.re_neg, mul_neg, mul_one] at hre
    have ha0 : a = 0 := by
      have hre' : -a = a := hre
      omega
    rw [ha0] at hnorm'
    have hbb : 2 * (b * b) = (p : ℤ) := by linear_combination hnorm'
    exact h2b b hbb

/-- **Enumeration of the units of ℤ[√−2].** The map $\{0, 1\} \to \mathbb{Z}[\sqrt{-2}]$ sending
$0$ to $1$ and $1$ to $-1$, which lists the two units of $\mathbb{Z}[\sqrt{-2}]$. -/
public def unitVal : Fin 2 → ℤ√(-2 : ℤ) :=
  fun i => if i = 0 then 1 else -1

/-- **The enumeration of the units of ℤ[√−2] is injective.** Let $\varepsilon_0 = 1$ and
$\varepsilon_1 = -1$ in $\mathbb{Z}[\sqrt{-2}]$. For $i, j \in \{0, 1\}$, if
$\varepsilon_i = \varepsilon_j$ then $i = j$. -/
public theorem unitVal_inj : Function.Injective unitVal := by
  intro i j h
  fin_cases i <;> fin_cases j <;> first | rfl | exact absurd h (by decide)

/-- **Every unit of ℤ[√−2] is enumerated.** Let $\varepsilon_0 = 1$ and $\varepsilon_1 = -1$ be the
enumeration of the units of $\mathbb{Z}[\sqrt{-2}]$. Every unit $u$ of $\mathbb{Z}[\sqrt{-2}]$
equals $\varepsilon_i$ for some $i \in \{0, 1\}$. -/
public theorem unitVal_complete (u : ℤ√(-2 : ℤ)) (hu : IsUnit u) :
    ∃ i, unitVal i = u := by
  rcases (zsqrtd_neg_two_isUnit_iff u).mp hu with rfl | rfl
  · exact ⟨0, by decide⟩
  · exact ⟨1, by decide⟩

/-- **Inverses of the enumerated units of ℤ[√−2].** The map $\{0, 1\} \to \mathbb{Z}[\sqrt{-2}]$
sending $0$ to $1$ and $1$ to $-1$. Since $1$ and $-1$ are their own inverses, its value at $i$ is
the inverse of the $i$-th enumerated unit. -/
public def unitValInv : Fin 2 → ℤ√(-2 : ℤ) :=
  fun i => if i = 0 then 1 else -1

/-- **Each enumerated unit of ℤ[√−2] times its listed inverse is one.** Let $\varepsilon_0 = 1$,
$\varepsilon_1 = -1$ be the enumerated units of $\mathbb{Z}[\sqrt{-2}]$ and $\eta_0 = 1$,
$\eta_1 = -1$ their listed inverses. Then $\varepsilon_i \eta_i = 1$ for each $i \in \{0, 1\}$. -/
public theorem unitVal_mul_unitValInv (i : Fin 2) :
    unitVal i * unitValInv i = 1 := by
  fin_cases i <;> decide

end

end Zsqrtd.NegTwo
