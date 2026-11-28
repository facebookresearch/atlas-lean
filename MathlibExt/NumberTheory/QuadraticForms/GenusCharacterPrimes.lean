/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.DirichletCharacter.Quadratic
public import Mathlib.Algebra.QuadraticDiscriminant
public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Mathlib.NumberTheory.LSeries.PrimesInAP
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.Linarith

/-!
# Primes with prescribed genus characters

Let $D$ be a fundamental discriminant. The genus characters of $D$ are the Legendre symbols
$\left(\frac{r}{p}\right)$ for the odd primes $p \mid D$, together with, when $D$ is even, one of
the characters $\xi(r) = \left(\frac{-1}{r}\right)$, $\eta(r) = \left(\frac{2}{r}\right)$ and
$\xi(r)\eta(r) = \left(\frac{-2}{r}\right)$ according as $D/4 \equiv 3 \pmod 4$,
$D/4 \equiv 2 \pmod 8$ or $D/4 \equiv 6 \pmod 8$.

This file proves that every system of signs $s_p = \pm 1$ indexed by the prime divisors of $D$
with $\prod_p s_p = 1$ is the system of genus character values of some prime $q$ that is coprime
to $2D$ and is the leading coefficient of an integral binary quadratic form $(q, b, c)$ of
discriminant $D$. This combines Knapp, *Advanced Algebra* (digital second edition, 2016),
Chapter I, Problems 38 and 39, p. 75: the prime $q$ comes from the Chinese remainder theorem and
Dirichlet's theorem on primes in arithmetic progressions, and the condition $\prod_p s_p = 1$
gives $\left(\frac{D}{q}\right) = 1$ by quadratic reciprocity (Problem 37), so that $D$ is a
square modulo $4q$.
-/

@[expose] public section

set_option autoImplicit false

namespace MetaMathlibExt

/-- **The $2$-adic genus character of a discriminant.** For an integer $D$ with $D \equiv 0
\pmod 4$, the value at $r$ is $\chi_4(r)$ if $D/4 \equiv 3 \pmod 4$, $\chi_8(r)$ if
$D/4 \equiv 2 \pmod 8$, and $\chi_8'(r)$ if $D/4 \equiv 6 \pmod 8$; in every other case the value
is $1$. Here $\chi_4(r) = \left(\frac{-1}{r}\right)$, $\chi_8(r) = \left(\frac{2}{r}\right)$ and
$\chi_8'(r) = \left(\frac{-2}{r}\right)$ for odd $r$ (Mathlib's `ZMod.χ₄`, `ZMod.χ₈`,
`ZMod.χ₈'`, which vanish at even $r$).

Source: Knapp, *Advanced Algebra* (digital second edition, 2016), Chapter I, the genus characters
defined before Problem 35, p. 74, which for even $D$ are $\xi(r) = \left(\frac{-1}{r}\right)$ if
$D/4 \equiv 3 \pmod 4$, $\eta(r) = \left(\frac{2}{r}\right)$ if $D/4 \equiv 2 \pmod 8$, and
$\xi(r)\eta(r) = \left(\frac{-2}{r}\right)$ if $D/4 \equiv 6 \pmod 8$; and Problem 38, p. 75:
"If D is even, let α be ξ if D/4 ≡ 3 mod 4, η if D/4 ≡ 2 mod 8, and ξ η if D/4 ≡ 6 mod 8."
The value `1` for odd $D$ is a convention of this definition. -/
def genusCharTwo (D r : ℤ) : ℤ :=
  if D % 4 = 0 ∧ (D / 4) % 4 = 3 then (ZMod.χ₄ (r : ZMod 4) : ℤ)
  else if D % 4 = 0 ∧ (D / 4) % 8 = 2 then (ZMod.χ₈ (r : ZMod 8) : ℤ)
  else if D % 4 = 0 ∧ (D / 4) % 8 = 6 then (ZMod.χ₈' (r : ZMod 8) : ℤ)
  else 1

private lemma genusCharTwo_eq_chi4 {D : ℤ} (h : D % 4 = 0 ∧ (D / 4) % 4 = 3) (r : ℕ) :
    genusCharTwo D r = ZMod.χ₄ (r : ZMod 4) := by
  simp only [genusCharTwo, ite_eq_left h, Int.cast_natCast]

private lemma genusCharTwo_eq_chi8 {D : ℤ} (h : D % 4 = 0 ∧ (D / 4) % 8 = 2) (r : ℕ) :
    genusCharTwo D r = ZMod.χ₈ (r : ZMod 8) := by
  have h1 : ¬ (D % 4 = 0 ∧ (D / 4) % 4 = 3) := by omega
  simp only [genusCharTwo, ite_eq_right h1, ite_eq_left h, Int.cast_natCast]

private lemma genusCharTwo_eq_chi8' {D : ℤ} (h : D % 4 = 0 ∧ (D / 4) % 8 = 6) (r : ℕ) :
    genusCharTwo D r = ZMod.χ₈' (r : ZMod 8) := by
  have h1 : ¬ (D % 4 = 0 ∧ (D / 4) % 4 = 3) := by omega
  have h2 : ¬ (D % 4 = 0 ∧ (D / 4) % 8 = 2) := by omega
  simp only [genusCharTwo, ite_eq_right h1, ite_eq_right h2, ite_eq_left h, Int.cast_natCast]

private lemma genusCharTwo_eq_one {D : ℤ} (h : D % 4 ≠ 0) (r : ℤ) : genusCharTwo D r = 1 := by
  have h1 : ¬ (D % 4 = 0 ∧ (D / 4) % 4 = 3) := by omega
  have h2 : ¬ (D % 4 = 0 ∧ (D / 4) % 8 = 2) := by omega
  have h3 : ¬ (D % 4 = 0 ∧ (D / 4) % 8 = 6) := by omega
  simp only [genusCharTwo, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]

private lemma genusCharTwo_congr (D : ℤ) {r r' : ℕ} (h : r % 8 = r' % 8) :
    genusCharTwo D r = genusCharTwo D r' := by
  have h8 : (r : ZMod 8) = r' := (ZMod.natCast_eq_natCast_iff' _ _ _).2 h
  have h4 : (r : ZMod 4) = r' := (ZMod.natCast_eq_natCast_iff' _ _ _).2 (by omega)
  simp only [genusCharTwo, Int.cast_natCast, h8, h4]

private lemma genusCharTwo_one (D : ℤ) : genusCharTwo D ((1 : ℕ) : ℤ) = 1 := by
  simp [genusCharTwo]

private lemma genusCharTwo_three_or_five {D : ℤ}
    (h : D % 4 = 0 ∧ ((D / 4) % 4 = 3 ∨ (D / 4) % 8 = 2 ∨ (D / 4) % 8 = 6)) :
    genusCharTwo D ((3 : ℕ) : ℤ) = -1 ∨ genusCharTwo D ((5 : ℕ) : ℤ) = -1 := by
  rcases h with ⟨h0, h1 | h1 | h1⟩
  · left
    rw [genusCharTwo_eq_chi4 ⟨h0, h1⟩, ZMod.χ₄_nat_eq_if_mod_four]
    norm_num
  · left
    rw [genusCharTwo_eq_chi8 ⟨h0, h1⟩, ZMod.χ₈_nat_eq_if_mod_eight]
    norm_num
  · right
    rw [genusCharTwo_eq_chi8' ⟨h0, h1⟩, ZMod.χ₈'_nat_eq_if_mod_eight]
    norm_num

/-- A fundamental discriminant is $\pm o$, $\pm 4 o$ or $\pm 8 o$ for an odd squarefree natural
number $o$, with the residues of $o$ modulo $4$ forced as listed. -/
private lemma exists_odd_part {D : ℤ} (hf : IsFundamentalDiscriminant D) :
    ∃ o : ℕ, o % 2 = 1 ∧ Squarefree o ∧
      ((D = o ∧ o % 4 = 1) ∨ (D = -o ∧ o % 4 = 3) ∨ (D = 4 * o ∧ o % 4 = 3) ∨
        (D = -(4 * o) ∧ o % 4 = 1) ∨ (D = 8 * o ∧ o % 4 = 1) ∨ (D = 8 * o ∧ o % 4 = 3) ∨
        (D = -(8 * o) ∧ o % 4 = 1) ∨ (D = -(8 * o) ∧ o % 4 = 3)) := by
  rcases hf with ⟨hsq, h4⟩ | ⟨m, rfl, hsq, hm⟩
  · exact ⟨D.natAbs, by omega, Int.squarefree_natAbs.2 hsq, by omega⟩
  · have hsq' : Squarefree m.natAbs := Int.squarefree_natAbs.2 hsq
    rcases hm with hm | hm
    · exact ⟨m.natAbs / 2, by omega,
        hsq'.squarefree_of_dvd (Nat.div_dvd_of_dvd (by omega)), by omega⟩
    · exact ⟨m.natAbs, by omega, hsq', by omega⟩

/-- The Jacobi symbol of `D` at an odd `q` is the `2`-adic genus character of `q` times the
Jacobi symbol of `q` at the odd part `o` of `D` (quadratic reciprocity). -/
private lemma jacobiSym_eq_genusCharTwo_mul {D : ℤ} {o q : ℕ} (hq : q % 2 = 1)
    (ho : o % 2 = 1)
    (hD : (D = o ∧ o % 4 = 1) ∨ (D = -o ∧ o % 4 = 3) ∨ (D = 4 * o ∧ o % 4 = 3) ∨
        (D = -(4 * o) ∧ o % 4 = 1) ∨ (D = 8 * o ∧ o % 4 = 1) ∨ (D = 8 * o ∧ o % 4 = 3) ∨
        (D = -(8 * o) ∧ o % 4 = 1) ∨ (D = -(8 * o) ∧ o % 4 = 3)) :
    jacobiSym D q = genusCharTwo D q * jacobiSym q o := by
  have hqodd : Odd q := Nat.odd_iff.2 hq
  have hoodd : Odd o := Nat.odd_iff.2 ho
  have hχ4 : (ZMod.χ₄ (q : ZMod 4) : ℤ) = if q % 4 = 1 then 1 else -1 := by
    rw [ZMod.χ₄_nat_eq_if_mod_four, ite_eq_right (by omega)]
  have hχ8 : (ZMod.χ₈ (q : ZMod 8) : ℤ) = if q % 8 = 1 ∨ q % 8 = 7 then 1 else -1 := by
    rw [ZMod.χ₈_nat_eq_if_mod_eight, ite_eq_right (by omega)]
  have hχ8' : (ZMod.χ₈' (q : ZMod 8) : ℤ) = if q % 8 = 1 ∨ q % 8 = 3 then 1 else -1 := by
    rw [ZMod.χ₈'_nat_eq_if_mod_eight, ite_eq_right (by omega)]
  have hm1 : jacobiSym (-1) q = if q % 4 = 1 then 1 else -1 := by
    rw [jacobiSym.at_neg_one hqodd, hχ4]
  have h2 : jacobiSym 2 q = if q % 8 = 1 ∨ q % 8 = 7 then 1 else -1 := by
    rw [jacobiSym.at_two hqodd, hχ8]
  have hrec : jacobiSym o q = (if o % 4 = 3 ∧ q % 4 = 3 then -1 else 1) * jacobiSym q o := by
    split_ifs with h
    · rw [jacobiSym.quadratic_reciprocity_three_mod_four h.1 h.2]
      ring
    · rcases (by omega : o % 4 = 1 ∨ q % 4 = 1) with h' | h'
      · rw [one_mul, jacobiSym.quadratic_reciprocity_one_mod_four h' hqodd]
      · rw [one_mul, jacobiSym.quadratic_reciprocity_one_mod_four' hoodd h']
  have hq8 : (q % 8 = 1 ∧ q % 4 = 1) ∨ (q % 8 = 3 ∧ q % 4 = 3) ∨ (q % 8 = 5 ∧ q % 4 = 1) ∨
      (q % 8 = 7 ∧ q % 4 = 3) := by omega
  rcases hD with ⟨rfl, ho4⟩ | ⟨rfl, ho4⟩ | ⟨rfl, ho4⟩ | ⟨rfl, ho4⟩ | ⟨rfl, ho4⟩ | ⟨rfl, ho4⟩ |
    ⟨rfl, ho4⟩ | ⟨rfl, ho4⟩
  · rw [genusCharTwo_eq_one (by omega), hrec]
    rcases hq8 with ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ <;> simp [h4, ho4]
  · rw [genusCharTwo_eq_one (by omega), show -(o : ℤ) = -1 * o by ring, jacobiSym.mul_left,
      hm1, hrec]
    rcases hq8 with ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ <;> simp [h4, ho4]
  · rw [genusCharTwo_eq_chi4 (by omega), hχ4, show (4 : ℤ) * o = 2 * 2 * o by ring,
      jacobiSym.mul_left, jacobiSym.mul_left, h2, hrec]
    rcases hq8 with ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ <;> simp [h8, h4, ho4]
  · rw [genusCharTwo_eq_chi4 (by omega), hχ4, show -((4 : ℤ) * o) = -1 * 2 * 2 * o by ring,
      jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left, hm1, h2, hrec]
    rcases hq8 with ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ <;> simp [h8, h4, ho4]
  · rw [genusCharTwo_eq_chi8 (by omega), hχ8, show (8 : ℤ) * o = 2 * 2 * 2 * o by ring,
      jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left, h2, hrec]
    rcases hq8 with ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ <;> simp [h8, h4, ho4]
  · rw [genusCharTwo_eq_chi8' (by omega), hχ8', show (8 : ℤ) * o = 2 * 2 * 2 * o by ring,
      jacobiSym.mul_left, jacobiSym.mul_left, jacobiSym.mul_left, h2, hrec]
    rcases hq8 with ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ <;> simp [h8, h4, ho4]
  · rw [genusCharTwo_eq_chi8' (by omega), hχ8',
      show -((8 : ℤ) * o) = -1 * 2 * 2 * 2 * o by ring, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.mul_left, jacobiSym.mul_left, hm1, h2, hrec]
    rcases hq8 with ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ <;> simp [h8, h4, ho4]
  · rw [genusCharTwo_eq_chi8 (by omega), hχ8,
      show -((8 : ℤ) * o) = -1 * 2 * 2 * 2 * o by ring, jacobiSym.mul_left, jacobiSym.mul_left,
      jacobiSym.mul_left, jacobiSym.mul_left, hm1, h2, hrec]
    rcases hq8 with ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ | ⟨h8, h4⟩ <;> simp [h8, h4, ho4]

private lemma jacobiSym_prod_right (a : ℤ) (S : Finset ℕ) (hS : ∀ p ∈ S, p ≠ 0) :
    jacobiSym a (∏ p ∈ S, p) = ∏ p ∈ S, jacobiSym a p := by
  induction S using Finset.induction_on with
  | empty => simp [jacobiSym.one_right]
  | insert x S hx ih =>
    have hS' : ∀ p ∈ S, p ≠ 0 := fun p hp => hS p (Finset.mem_insert_of_mem hp)
    rw [Finset.prod_insert hx, Finset.prod_insert hx,
      jacobiSym.mul_right' a (hS x (Finset.mem_insert_self x S))
        (Finset.prod_ne_zero_iff.2 hS'), ih hS']

private lemma exists_jacobiSym_eq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : ℤ}
    (ht : t = 1 ∨ t = -1) : ∃ a : ℕ, jacobiSym a p = t := by
  rcases ht with rfl | rfl
  · exact ⟨1, by simp [jacobiSym.one_left]⟩
  · have : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hx⟩ := FiniteField.exists_nonsquare (F := ZMod p)
      (by rw [ZMod.ringChar_zmod_n]; exact hp2)
    refine ⟨x.val, ?_⟩
    rw [← jacobiSym.legendreSym.to_jacobiSym, legendreSym.eq_neg_one_iff]
    simpa using hx

/-- **Primes with prescribed genus characters, represented by a form of discriminant $D$.** Let
$D$ be a fundamental discriminant and let $p \mapsto s_p$ assign a sign $\pm 1$ to each prime
divisor $p$ of $D$, with $\prod_{p \mid D} s_p = 1$. Then there is a prime $q$ coprime to $2D$
such that the Jacobi symbol $\left(\frac{q}{p}\right)$ equals $s_p$ for each odd prime $p \mid D$,
the $2$-adic genus character `genusCharTwo D q` equals $s_2$ when $D$ is even, and
$D = b^2 - 4qc$ for some integers $b, c$, so that $q$ is represented (primitively, by $(1, 0)$)
by the integral binary quadratic form $q x^2 + b x y + c y^2$ of discriminant $D$.

The sign of $D$ plays no role: the statement holds for positive and negative fundamental
discriminants alike, so no hypothesis $D < 0$ is assumed. The form is exhibited through its
coefficients and discriminant (Mathlib's `discrim`). The genus characters are evaluated at $q$;
this file does not formalize them as functions on forms or similarity classes, nor the count of
similarity classes that Problem 39 concludes with.

Source: Knapp, *Advanced Algebra* (digital second edition, 2016), Chapter I, Problem 38, p. 75:
"Let p ↦ s_p be any function to {±1} from the set of distinct prime divisors of D. Using
Dirichlet's Theorem on primes in arithmetic progressions, prove that there exists a prime q such
that (q/p) = s_p for each odd prime divisor p of D and α(q) = s_2 in case D is even", and
Problem 39, p. 75: "let p ↦ s_p be any function to {±1} from the set of distinct prime divisors
of D such that ∏_p s_p = +1, and choose a prime q as in the previous problem. Prove that q is
primitively representable by some integer binary quadratic form of discriminant D and that the
values of the genus characters on this form are the numbers s_p." The genus characters are
defined before Problem 35, p. 74. -/
theorem exists_prime_genusCharacters {D : ℤ} (hf : IsFundamentalDiscriminant D)
    (s : ℕ → ℤ) (hs : ∀ p ∈ D.natAbs.primeFactors, s p = 1 ∨ s p = -1)
    (hprod : ∏ p ∈ D.natAbs.primeFactors, s p = 1) :
    ∃ q : ℕ, q.Prime ∧ Nat.Coprime q (2 * D.natAbs) ∧
      (∀ p ∈ D.natAbs.primeFactors, p ≠ 2 → jacobiSym (q : ℤ) p = s p) ∧
      (2 ∈ D.natAbs.primeFactors → genusCharTwo D q = s 2) ∧
      ∃ b c : ℤ, discrim (q : ℤ) b c = D := by
  obtain ⟨o, ho, hsq, hD⟩ := exists_odd_part hf
  have hn : D.natAbs = o ∨ D.natAbs = 4 * o ∨ D.natAbs = 8 * o := by omega
  have hn0 : D.natAbs ≠ 0 := by omega
  have hD4 : D % 4 = 0 ∨ D % 4 = 1 := by omega
  have hoddp : ∀ p ∈ o.primeFactors, p.Prime ∧ p ≠ 2 := fun p hp => by
    have hp' := Nat.mem_primeFactors.1 hp
    refine ⟨hp'.1, fun h => ?_⟩
    have h2 := hp'.2.1
    rw [h] at h2
    omega
  have hmem : ∀ p, (p ∈ D.natAbs.primeFactors ∧ p ≠ 2) ↔ p ∈ o.primeFactors := by
    intro p
    simp only [Nat.mem_primeFactors]
    constructor
    · rintro ⟨⟨hp, hpd, -⟩, hp2⟩
      have hcop : Nat.Coprime p (2 ^ 3) :=
        ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right 3
      refine ⟨hp, ?_, by omega⟩
      rcases hn with h | h | h <;> rw [h] at hpd
      · exact hpd
      · exact (hcop.coprime_dvd_right (by norm_num)).dvd_of_dvd_mul_left hpd
      · exact hcop.dvd_of_dvd_mul_left hpd
    · rintro ⟨hp, hpd, -⟩
      refine ⟨⟨hp, ?_, hn0⟩, ?_⟩
      · rcases hn with h | h | h <;> rw [h]
        · exact hpd
        · exact Dvd.dvd.mul_left hpd 4
        · exact Dvd.dvd.mul_left hpd 8
      · rintro rfl
        omega
  have h2mem : 2 ∈ D.natAbs.primeFactors ↔ D % 2 = 0 := by
    simp only [Nat.mem_primeFactors, Nat.prime_two, true_and, ne_eq, hn0, not_false_eq_true,
      and_true]
    omega
  -- residues modulo the odd primes
  have hres : ∀ p ∈ o.primeFactors, ∃ a : ℕ, jacobiSym a p = s p := fun p hp =>
    exists_jacobiSym_eq (hoddp p hp).1 (hoddp p hp).2 (hs p ((hmem p).2 hp).1)
  choose! a ha using hres
  -- residue modulo 8
  obtain ⟨a2, ha2, ha2s⟩ : ∃ a2 : ℕ, a2 % 2 = 1 ∧ (D % 2 = 0 → genusCharTwo D a2 = s 2) := by
    by_cases hD2 : D % 2 = 0
    · rcases hs 2 (h2mem.2 hD2) with h | h
      · exact ⟨1, rfl, fun _ => by rw [genusCharTwo_one, h]⟩
      · rcases genusCharTwo_three_or_five (D := D) (by omega) with h' | h'
        · exact ⟨3, rfl, fun _ => by rw [h', h]⟩
        · exact ⟨5, rfl, fun _ => by rw [h', h]⟩
    · exact ⟨1, rfl, fun h => absurd h hD2⟩
  -- Chinese remainder theorem
  have hmd : ∀ i ∈ insert 2 o.primeFactors, (fun i => if i = 2 then 8 else i) i ≠ 0 := by
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · simp
    · simp only [ite_eq_right (hoddp i hi).2]
      exact (hoddp i hi).1.ne_zero
  have hpw : (↑(insert 2 o.primeFactors) : Set ℕ).Pairwise
      (Function.onFun Nat.Coprime fun i => if i = 2 then 8 else i) := by
    intro i hi j hj hij
    simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at hi hj
    simp only [Function.onFun]
    rcases hi with rfl | hi <;> rcases hj with rfl | hj
    · exact absurd rfl hij
    · rw [ite_eq_left rfl, ite_eq_right (hoddp j hj).2]
      exact ((Nat.coprime_primes Nat.prime_two (hoddp j hj).1).2
        (hoddp j hj).2.symm).pow_left 3
    · rw [ite_eq_left rfl, ite_eq_right (hoddp i hi).2]
      exact ((Nat.coprime_primes (hoddp i hi).1 Nat.prime_two).2 (hoddp i hi).2).pow_right 3
    · rw [ite_eq_right (hoddp i hi).2, ite_eq_right (hoddp j hj).2]
      exact (Nat.coprime_primes (hoddp i hi).1 (hoddp j hj).1).2 hij
  obtain ⟨k, hk⟩ := Nat.chineseRemainderOfFinset (fun i => if i = 2 then a2 else a i)
    (fun i => if i = 2 then 8 else i) (insert 2 o.primeFactors) hmd hpw
  have hk8 : k % 8 = a2 % 8 := by
    simpa [Nat.ModEq] using hk 2 (Finset.mem_insert_self _ _)
  have hkp : ∀ p ∈ o.primeFactors, k % p = a p % p := fun p hp => by
    simpa [Nat.ModEq, (hoddp p hp).2] using hk p (Finset.mem_insert_of_mem hp)
  have hJk : ∀ p ∈ o.primeFactors, jacobiSym k p = s p := fun p hp => by
    rw [← ha p hp]
    apply jacobiSym.mod_left'
    rw [← Int.natCast_mod, ← Int.natCast_mod, hkp p hp]
  have hcop : Nat.Coprime k (8 * o) := by
    apply Nat.Coprime.mul_right
    · have h8 : Nat.Coprime (2 ^ 3) k :=
        ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)).pow_left 3
      exact h8.symm
    · rw [← Nat.prod_primeFactors_of_squarefree hsq]
      apply Nat.Coprime.prod_right
      intro p hp
      have : NeZero p := ⟨(hoddp p hp).1.ne_zero⟩
      have hne : jacobiSym k p ≠ 0 := by
        rw [hJk p hp]
        rcases hs p ((hmem p).2 hp).1 with h | h <;> rw [h] <;> norm_num
      have hg := not_not.1 (mt jacobiSym.eq_zero_iff_not_coprime.2 hne)
      rw [Int.gcd_natCast_natCast] at hg
      exact hg
  -- Dirichlet's theorem
  have : NeZero (8 * o) := ⟨by omega⟩
  obtain ⟨q, hqgt, hq, hqk⟩ := Nat.forall_exists_prime_gt_and_eq_mod
    ((ZMod.isUnit_iff_coprime k (8 * o)).2 hcop) (2 * D.natAbs)
  have hqk' : q ≡ k [MOD 8 * o] := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hqk
  have hq8 : q % 8 = a2 % 8 := by
    rw [← hk8]
    exact Nat.ModEq.of_dvd (Dvd.intro o rfl) hqk'
  have hqodd : q % 2 = 1 := by omega
  have hJq : ∀ p ∈ o.primeFactors, jacobiSym q p = s p := fun p hp => by
    rw [← hJk p hp]
    apply jacobiSym.mod_left'
    rw [← Int.natCast_mod, ← Int.natCast_mod,
      Nat.ModEq.of_dvd (Dvd.dvd.mul_left (Nat.dvd_of_mem_primeFactors hp) 8) hqk']
  have hgq : genusCharTwo D q = genusCharTwo D a2 := genusCharTwo_congr D hq8
  have hcopq : Nat.Coprime q (2 * D.natAbs) :=
    (Nat.coprime_or_dvd_of_prime hq _).resolve_right fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega
  -- quadratic reciprocity
  have hJo : jacobiSym q o = ∏ p ∈ o.primeFactors, jacobiSym q p := by
    have := jacobiSym_prod_right (q : ℤ) o.primeFactors (fun p hp => (hoddp p hp).1.ne_zero)
    rwa [Nat.prod_primeFactors_of_squarefree hsq] at this
  have hJD : jacobiSym D q = 1 := by
    rw [jacobiSym_eq_genusCharTwo_mul hqodd ho hD, ← hprod,
      ← Finset.prod_filter_mul_prod_filter_not D.natAbs.primeFactors (· = 2),
      Finset.filter_eq']
    have hfil : {x ∈ D.natAbs.primeFactors | ¬x = 2} = o.primeFactors := by
      ext p
      simp only [Finset.mem_filter]
      exact hmem p
    rw [hfil, hJo, Finset.prod_congr rfl hJq]
    split_ifs with h2
    · rw [Finset.prod_singleton, hgq, ha2s (h2mem.1 h2)]
    · rw [Finset.prod_empty, genusCharTwo_eq_one (by rw [h2mem] at h2; omega)]
  -- a square root of D modulo 4q
  have : Fact q.Prime := ⟨hq⟩
  obtain ⟨r, hr⟩ := ZMod.isSquare_of_jacobiSym_eq_one hJD
  have hb0 : (q : ℤ) ∣ (r.val : ℤ) ^ 2 - D := by
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val, hr]
    ring
  obtain ⟨b, hbq, hb2⟩ : ∃ b : ℤ, (q : ℤ) ∣ b ^ 2 - D ∧ b % 2 = D % 2 := by
    by_cases h : (r.val : ℤ) % 2 = D % 2
    · exact ⟨r.val, hb0, h⟩
    · refine ⟨r.val + q, ?_, by omega⟩
      have hsq' : ((r.val : ℤ) + q) ^ 2 - D = ((r.val : ℤ) ^ 2 - D) + q * (2 * r.val + q) := by
        ring
      rw [hsq']
      exact dvd_add hb0 (dvd_mul_right _ _)
  have h4 : (4 : ℤ) ∣ b ^ 2 - D := by
    obtain ⟨t, rfl | rfl⟩ := Int.even_or_odd' b
    · have ht : (2 * t) ^ 2 - D = 4 * t ^ 2 - D := by ring
      rw [ht]
      generalize t ^ 2 = u
      omega
    · have ht : (2 * t + 1) ^ 2 - D = 4 * (t ^ 2 + t) + 1 - D := by ring
      rw [ht]
      generalize t ^ 2 + t = u
      omega
  have hc4 : Nat.Coprime (2 ^ 2) q :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).2 (by omega)).pow_left 2
  have hcop4 : IsCoprime (4 : ℤ) q := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    exact hc4
  obtain ⟨c, hc⟩ := hcop4.mul_dvd h4 hbq
  refine ⟨q, hq, hcopq, fun p hp hp2 => hJq p ((hmem p).1 ⟨hp, hp2⟩), fun h2 => ?_, b, c, ?_⟩
  · rw [hgq]
    exact ha2s (h2mem.1 h2)
  · rw [discrim]
    linarith

end MetaMathlibExt
