/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Zsqrtd.Basic
public import Mathlib.NumberTheory.Zsqrtd.GaussianInt
public import Mathlib.NumberTheory.SumTwoSquares
public import Mathlib.RingTheory.UniqueFactorizationDomain.Basic
public import Mathlib.Order.Interval.Finset.Basic
public import Mathlib.Data.Int.Interval
public import Mathlib.Data.Fintype.Card
public import Mathlib.Tactic.LinearCombination
public import MathlibExt.NumberTheory.GaussianIntPrimeBasics

/-!
# Gaussian split primes

Primes `p ≡ 1 mod 4` split in the Gaussian integers `ℤ[i]`, and the count of
representations of prime powers `p ^ e` as a norm.
-/

local notation "ℤ[i]" => GaussianInt

namespace GaussianInt

@[expose] public section

/-- **Primes congruent to 1 mod 4 split in the Gaussian integers.** Let $p$ be a prime with
$p \equiv 1 \pmod 4$. Then there is a prime element $\pi = a + bi$ of $\mathbb{Z}[i]$ whose norm
$N(\pi) = a^2 + b^2$ equals $p$. -/
public theorem gaussianInt_split_prime {p : ℕ} [Fact p.Prime] (h : p % 4 = 1) :
    ∃ π : ℤ[i], Zsqrtd.norm π = p ∧ Prime π := by
  have hne : p % 4 ≠ 3 := by omega
  obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq hne
  have hcast : (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ) := by exact_mod_cast hab
  have hnorm : Zsqrtd.norm (⟨(a : ℤ), (b : ℤ)⟩ : ℤ[i]) = (p : ℤ) := by
    rw [Zsqrtd.norm_def]
    linear_combination hcast
  refine ⟨⟨(a : ℤ), (b : ℤ)⟩, hnorm, ?_⟩
  apply gaussianInt_prime_of_natAbs_norm_prime
  rw [hnorm, Int.natAbs_natCast]
  exact Fact.out


/-- **Factoring a prime as a Gaussian integer times its conjugate.** Let $p$ be a prime, write
$N(a + bi) = a^2 + b^2$ for the norm on $\mathbb{Z}[i]$, and let $\pi \in \mathbb{Z}[i]$ satisfy
$N(\pi) = p$. Then $p = \pi \bar{\pi}$ in $\mathbb{Z}[i]$, where $\bar{\pi}$ is the complex
conjugate of $\pi$, and $\bar{\pi}$ is a prime element of $\mathbb{Z}[i]$. -/
public theorem gaussianInt_split_conj {p : ℕ} [Fact p.Prime] {π : ℤ[i]}
    (hnorm : Zsqrtd.norm π = p) :
    (p : ℤ[i]) = π * star π ∧ Prime (star π) := by
  have h := Zsqrtd.norm_eq_mul_conj π
  rw [hnorm] at h
  refine ⟨?_, ?_⟩
  · exact_mod_cast h
  · apply gaussianInt_prime_of_natAbs_norm_prime
    rw [Zsqrtd.norm_conj, hnorm, Int.natAbs_natCast]
    exact Fact.out


/-- **Gaussian integers of split prime norm are not associate to their conjugates.** Write
$N(a + bi) = a^2 + b^2$ for the norm on $\mathbb{Z}[i]$. Let $p$ be a prime with
$p \equiv 1 \pmod 4$ and let $\pi \in \mathbb{Z}[i]$ satisfy $N(\pi) = p$. Then the complex
conjugate $\bar{\pi}$ is not associated to $\pi$: there is no unit $u$ of $\mathbb{Z}[i]$ with
$\bar{\pi} u = \pi$. -/
public theorem gaussianInt_split_nonassociated {p : ℕ} [Fact p.Prime] {π : ℤ[i]}
    (hnorm : Zsqrtd.norm π = p) (h1 : p % 4 = 1) :
    ¬ Associated (star π) π := by
  have hp : p.Prime := Fact.out
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
  have htwo : ∀ c : ℤ, 2 * (c * c) = (p : ℤ) → False := by
    intro c hc
    have hcc : 2 * (c.natAbs * c.natAbs) = p := by
      have h2 := congrArg Int.natAbs hc
      simpa [Int.natAbs_mul, Int.natAbs_natCast] using h2
    have hdvd : c.natAbs * c.natAbs ∣ p := ⟨2, by rw [mul_comm]; exact hcc.symm⟩
    rcases hp.eq_one_or_self_of_dvd _ hdvd with h1' | h1'
    · rw [h1', mul_one] at hcc
      subst hcc
      exact absurd h1 (by decide)
    · rw [h1'] at hcc
      have hp0 : p = 0 := by omega
      exact hp.ne_zero hp0
  intro hassoc
  obtain ⟨a, b⟩ := π
  obtain ⟨u, hu⟩ := hassoc
  have hu4 := (gaussianInt_isUnit_iff (u : ℤ[i])).mp u.isUnit
  rw [Zsqrtd.norm_def] at hnorm
  rcases hu4 with hcase | hcase | hcase | hcase
  · -- u = 1
    rw [hcase, mul_one] at hu
    have him := congrArg Zsqrtd.im hu
    simp only [Zsqrtd.im_star] at him
    have hb0 : b = 0 := by omega
    rw [hb0] at hnorm
    have haa : a * a = (p : ℤ) := by linear_combination hnorm
    exact hsq a haa
  · -- u = -1
    rw [hcase, show (-1 : ℤ[i]) = ⟨-1, 0⟩ from rfl] at hu
    have hre := congrArg Zsqrtd.re hu
    simp only [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star] at hre
    have ha0 : a = 0 := by linarith
    rw [ha0] at hnorm
    have hbb : b * b = (p : ℤ) := by linear_combination hnorm
    exact hsq b hbb
  · -- u = I
    rw [hcase] at hu
    have hre := congrArg Zsqrtd.re hu
    simp only [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star] at hre
    have hab : a = b := by linarith
    subst hab
    have h2 : 2 * (a * a) = (p : ℤ) := by linear_combination hnorm
    exact htwo a h2
  · -- u = -I
    rw [hcase] at hu
    have hre := congrArg Zsqrtd.re hu
    simp only [Zsqrtd.re_mul, Zsqrtd.re_star, Zsqrtd.im_star] at hre
    have hab : a = -b := by linarith
    subst hab
    have h2 : 2 * (b * b) = (p : ℤ) := by linear_combination hnorm
    exact htwo b h2


/-- Elements of `ℤ[i]` with norm `natAbs` equal to `n` form a finite type. -/
public noncomputable instance gaussianIntReprFintype (n : ℕ) :
    Fintype {α : ℤ[i] // (Zsqrtd.norm α).natAbs = n} := by
  have hnn2 : (n : ℤ) ≤ (n : ℤ) * n := by
    rcases Nat.eq_zero_or_pos n with rfl | hpos
    · simp
    · have h1 : (1 : ℤ) ≤ n := by exact_mod_cast hpos
      have h := mul_le_mul_of_nonneg_right h1 (show (0 : ℤ) ≤ (n : ℤ) by positivity)
      rwa [one_mul] at h
  have hbound : ∀ c : ℤ, c * c ≤ (n : ℤ) → |c| ≤ (n : ℤ) := by
    intro c hc
    have h2 : c ^ 2 ≤ (n : ℤ) ^ 2 := by
      rw [pow_two, pow_two]
      exact le_trans hc hnn2
    have h3 := sq_le_sq.mp h2
    rwa [abs_of_nonneg (show (0 : ℤ) ≤ (n : ℤ) by positivity)] at h3
  classical
  apply Fintype.ofInjective
    (fun a : {α : ℤ[i] // (Zsqrtd.norm α).natAbs = n} =>
      (⟨(a.1.re, a.1.im), by
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        have hnn := GaussianInt.norm_nonneg a.1
        have hnorm : Zsqrtd.norm a.1 = (n : ℤ) := by
          have h := Int.natAbs_of_nonneg hnn
          rw [a.2] at h
          exact h.symm
        rw [Zsqrtd.norm_def] at hnorm
        have hdecomp : a.1.re * a.1.re + a.1.im * a.1.im = (n : ℤ) := by
          linear_combination hnorm
        have him0 : 0 ≤ a.1.im * a.1.im := mul_self_nonneg _
        have hre0 : 0 ≤ a.1.re * a.1.re := mul_self_nonneg _
        have hre : a.1.re * a.1.re ≤ (n : ℤ) := by linarith
        have him : a.1.im * a.1.im ≤ (n : ℤ) := by linarith
        rw [← abs_le, ← abs_le]
        exact ⟨hbound _ hre, hbound _ him⟩⟩ :
        Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)))
  intro a b hab
  have hpair : (a.1.re, a.1.im) = (b.1.re, b.1.im) := congrArg Subtype.val hab
  rw [Prod.mk.injEq] at hpair
  exact Subtype.ext (Zsqrtd.ext hpair.1 hpair.2)


/-- **Number of Gaussian integers of norm a power of a split prime.** Write
$N(a + bi) = a^2 + b^2$ for the norm on $\mathbb{Z}[i]$. Let $p$ be a prime with
$p \equiv 1 \pmod 4$, let $e$ be a natural number, and suppose $\pi \in \mathbb{Z}[i]$ is a prime
element with $N(\pi) = p$. Then exactly $4(e + 1)$ Gaussian integers $\alpha$ satisfy
$|N(\alpha)| = p^e$. -/
public theorem gaussianInt_card_repr_prime_pow {p e : ℕ} [Fact p.Prime]
    (h1 : p % 4 = 1) {π : ℤ[i]} (hnorm : Zsqrtd.norm π = p)
    (hprime : Prime π) :
    Fintype.card {α : ℤ[i] // (Zsqrtd.norm α).natAbs = p ^ e} = 4 * (e + 1) :=
  Zsqrtd.card_norm_split_pow (by norm_num) unitVal unitValInv unitVal_mul_unitValInv
    unitVal_inj unitVal_complete hnorm hprime (gaussianInt_split_conj hnorm).1
    (gaussianInt_split_conj hnorm).2 (gaussianInt_split_nonassociated hnorm h1)

end

end GaussianInt
