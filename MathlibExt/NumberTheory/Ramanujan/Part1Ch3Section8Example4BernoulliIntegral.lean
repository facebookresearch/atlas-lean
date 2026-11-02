/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.NumberTheory.Bernoulli
public import MathlibExt.NumberTheory.Ramanujan.Part1Ch3Section8Example4Integrable
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Data.Rat.Star
import Mathlib.NumberTheory.BernoulliPolynomials

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Section 8, Example 4

`∫₀¹ x f(m - 1, t x) dt = ∑_{k ≤ m} C(m, k) B_{m-k} f(k, x) / (k + 1)`, where for `n ≥ 0`,
`f(n, x) = e^{-x} ∑_j (j + 1)ⁿ x^{j+1} / j!` is the Touchard polynomial of degree `n + 1`.
-/

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Section8Example4BernoulliIntegral

open Section8Example4Integrable (f f_natCast)
open Entry9IiGeneralizedbellgeneratingDefining (generalizedBellGenerating)

private lemma neg_one_le_natCast (k : ℕ) : (-1 : ℤ) ≤ k := by
  omega

private theorem choose_helper (p j : ℕ) (h : j ≤ p) :
    ((p - j : ℕ) : ℚ) * (Nat.choose p j : ℚ)
      = (p : ℚ) * (Nat.choose (p - 1) j : ℚ) := by
  rcases eq_or_lt_of_le h with hjp | hlt
  · rw [hjp, Nat.sub_self, Nat.cast_zero, zero_mul]
    by_cases hp : p = 0
    · subst hp; simp
    · have hz : (p - 1).choose p = 0 := Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, Nat.cast_zero, mul_zero]
  · have h1 : j ≤ p - 1 := by omega
    have e1 := Nat.choose_mul_factorial_mul_factorial h
    have e2 := Nat.choose_mul_factorial_mul_factorial h1
    have c1 : (Nat.choose p j : ℚ) * (Nat.factorial j : ℚ) * (Nat.factorial (p - j) : ℚ)
        = (Nat.factorial p : ℚ) := by exact_mod_cast e1
    have c2 : (Nat.choose (p - 1) j : ℚ) * (Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ)
        = (Nat.factorial (p - 1) : ℚ) := by exact_mod_cast e2
    have hsub : p - j - 1 = p - 1 - j := by omega
    have hfact1 : (Nat.factorial (p - j) : ℚ)
        = ((p - j : ℕ) : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ) := by
      have e : p - j = (p - 1 - j) + 1 := by omega
      rw [e, Nat.factorial_succ]
      push_cast
      ring
    have hfact2 : (Nat.factorial p : ℚ) = (p : ℚ) * (Nat.factorial (p - 1) : ℚ) := by
      have e : p = (p - 1) + 1 := by omega
      rw [e, Nat.factorial_succ]
      push_cast
      ring
    have jf : (Nat.factorial j : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have mf : (Nat.factorial ((p - 1) - j) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have key1 : ((p - j : ℕ) : ℚ) * (Nat.choose p j : ℚ) * (Nat.factorial j : ℚ)
          * (Nat.factorial ((p - 1) - j) : ℚ) = (Nat.factorial p : ℚ) := by
      have : (Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ) * ((p - j : ℕ) : ℚ)
          = (Nat.factorial j : ℚ) * (Nat.factorial (p - j) : ℚ) := by
        rw [hfact1]; ring
      calc ((p - j : ℕ) : ℚ) * (Nat.choose p j : ℚ) * (Nat.factorial j : ℚ)
              * (Nat.factorial ((p - 1) - j) : ℚ)
          = (Nat.choose p j : ℚ) * ((Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ)
              * ((p - j : ℕ) : ℚ)) := by ring
        _ = (Nat.choose p j : ℚ) * ((Nat.factorial j : ℚ) * (Nat.factorial (p - j) : ℚ)) := by
            rw [this]
        _ = (Nat.factorial p : ℚ) := by rw [← c1]; ring
    have key2 : (p : ℚ) * (Nat.choose (p - 1) j : ℚ) * (Nat.factorial j : ℚ)
          * (Nat.factorial ((p - 1) - j) : ℚ) = (Nat.factorial p : ℚ) := by
      calc (p : ℚ) * (Nat.choose (p - 1) j : ℚ) * (Nat.factorial j : ℚ)
              * (Nat.factorial ((p - 1) - j) : ℚ)
          = (p : ℚ) * ((Nat.choose (p - 1) j : ℚ) * (Nat.factorial j : ℚ)
              * (Nat.factorial ((p - 1) - j) : ℚ)) := by ring
        _ = (p : ℚ) * (Nat.factorial (p - 1) : ℚ) := by rw [c2]
        _ = (Nat.factorial p : ℚ) := hfact2.symm
    have hfac : (Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ) ≠ 0 :=
      mul_ne_zero jf mf
    have heq : (((p - j : ℕ)) : ℚ) * (Nat.choose p j : ℚ)
          * ((Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ))
          = (p : ℚ) * (Nat.choose (p - 1) j : ℚ)
          * ((Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ)) := by
      have k1 := key1
      have k2 := key2
      have r1 : ((p - j : ℕ) : ℚ) * (Nat.choose p j : ℚ)
          * ((Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ))
          = (Nat.factorial p : ℚ) := by
        calc ((p - j : ℕ) : ℚ) * (Nat.choose p j : ℚ)
              * ((Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ))
            = ((p - j : ℕ) : ℚ) * (Nat.choose p j : ℚ) * (Nat.factorial j : ℚ)
              * (Nat.factorial ((p - 1) - j) : ℚ) := by ring
          _ = (Nat.factorial p : ℚ) := k1
      have r2 : (p : ℚ) * (Nat.choose (p - 1) j : ℚ)
          * ((Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ))
          = (Nat.factorial p : ℚ) := by
        calc (p : ℚ) * (Nat.choose (p - 1) j : ℚ)
              * ((Nat.factorial j : ℚ) * (Nat.factorial ((p - 1) - j) : ℚ))
            = (p : ℚ) * (Nat.choose (p - 1) j : ℚ) * (Nat.factorial j : ℚ)
              * (Nat.factorial ((p - 1) - j) : ℚ) := by ring
          _ = (Nat.factorial p : ℚ) := k2
      rw [r1, r2]
    exact mul_right_cancel₀ hfac heq

/-- Recurrence for the alternating binomial power sums. -/
private theorem Rstep (p i : ℕ) :
    (∑ j ∈ Finset.range (p + 2), ((-1 : ℚ) ^ (p + 1 - j)) * (Nat.choose (p + 1) j : ℚ)
      * ((j : ℚ) ^ (i + 1)))
    = (((p + 1 : ℕ)) : ℚ) * (∑ j ∈ Finset.range (p + 2), ((-1 : ℚ) ^ (p + 1 - j))
      * (Nat.choose (p + 1) j : ℚ) * ((j : ℚ) ^ i))
    + (((p + 1 : ℕ)) : ℚ) * (∑ j ∈ Finset.range (p + 1), ((-1 : ℚ) ^ (p - j))
      * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i)) := by
  have per : ∀ j ∈ Finset.range (p + 2),
      ((-1 : ℚ) ^ (p + 1 - j)) * (Nat.choose (p + 1) j : ℚ) * ((j : ℚ) ^ (i + 1))
      - ((((p + 1 : ℕ))) : ℚ) * (((-1 : ℚ) ^ (p + 1 - j)) * (Nat.choose (p + 1) j : ℚ)
        * ((j : ℚ) ^ i))
      = ((((p + 1 : ℕ))) : ℚ) * (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)
        * ((j : ℚ) ^ i)) := by
    intro j hj
    by_cases hjj : j = p + 1
    · subst hjj
      have hz : (Nat.choose p (p + 1) : ℚ) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt (Nat.lt_succ_self p)
      rw [show p + 1 - (p + 1) = 0 from Nat.sub_self _,
        show p - (p + 1) = 0 from by omega,
        pow_zero, Nat.choose_self, one_mul, hz]
      simp only [mul_zero]
      rw [pow_succ]
      ring
    · have hjle : j ≤ p := by
        have := Finset.mem_range.mp hj
        omega
      have hjle1 : j ≤ p + 1 := by omega
      have ch := choose_helper (p + 1) j hjle1
      rw [Nat.add_sub_cancel] at ch
      have hcast : ((j : ℚ) - ((((p + 1 : ℕ))) : ℚ)) = -((((p + 1 - j : ℕ))) : ℚ) := by
        have e : (p + 1 - j : ℕ) + j = p + 1 := by omega
        have he : ((((p + 1 - j : ℕ))) : ℚ) + (j : ℚ) = ((((p + 1 : ℕ))) : ℚ) := by
          exact_mod_cast e
        linarith
      have hpow : ((-1 : ℚ) ^ (p + 1 - j)) = ((-1 : ℚ) ^ (p - j)) * (-1) := by
        have e : p + 1 - j = (p - j) + 1 := by omega
        rw [e, pow_succ]
      rw [hpow, pow_succ]
      linear_combination (((-1 : ℚ) ^ (p - j)) * ((j : ℚ) ^ i)) * ch
        - (((-1 : ℚ) ^ (p - j)) * ((j : ℚ) ^ i) * (Nat.choose (p + 1) j : ℚ)) * hcast
  have hsum : (∑ j ∈ Finset.range (p + 2),
        (((-1 : ℚ) ^ (p + 1 - j)) * (Nat.choose (p + 1) j : ℚ) * ((j : ℚ) ^ (i + 1))
        - ((((p + 1 : ℕ))) : ℚ) * (((-1 : ℚ) ^ (p + 1 - j)) * (Nat.choose (p + 1) j : ℚ)
          * ((j : ℚ) ^ i))))
      = ∑ j ∈ Finset.range (p + 2), ((((p + 1 : ℕ))) : ℚ) * (((-1 : ℚ) ^ (p - j))
        * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i)) :=
    Finset.sum_congr rfl (fun j hj => per j hj)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum] at hsum
  have peel : ((((p + 1 : ℕ))) : ℚ) * (∑ j ∈ Finset.range (p + 2), ((-1 : ℚ) ^ (p - j))
      * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i))
      = ((((p + 1 : ℕ))) : ℚ) * (∑ j ∈ Finset.range (p + 1), ((-1 : ℚ) ^ (p - j))
        * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i)) := by
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_range_succ]
    have hz : (Nat.choose p (p + 1) : ℚ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt (Nat.lt_succ_self p)
    rw [hz]
    simp
  linear_combination hsum + peel

/-- Explicit formula for Stirling numbers of the second kind. -/
private theorem stirling_explicit (p : ℕ) : ∀ i : ℕ,
    (∑ j ∈ Finset.range (p + 1), ((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)
      * ((j : ℚ) ^ i))
    = (Nat.factorial p : ℚ) * (Nat.stirlingSecond i p : ℚ) := by
  induction p with
  | zero =>
    intro i
    rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    cases i with
    | zero =>
      rw [pow_zero, Nat.stirlingSecond_zero]
      norm_num
    | succ i =>
      rw [show ((0 : ℕ) : ℚ) = 0 from Nat.cast_zero, zero_pow (Nat.succ_ne_zero _),
        show Nat.stirlingSecond (i + 1) 0 = 0 from Nat.stirlingSecond_succ_zero _]
      norm_num
  | succ p ih =>
    intro i
    change (∑ j ∈ Finset.range (p + 2), ((-1 : ℚ) ^ (p + 1 - j))
        * (Nat.choose (p + 1) j : ℚ) * ((j : ℚ) ^ i))
      = (Nat.factorial (p + 1) : ℚ) * (Nat.stirlingSecond i (p + 1) : ℚ)
    induction i with
    | zero =>
      have hR : (∑ j ∈ Finset.range (p + 2), ((-1 : ℚ) ^ (p + 1 - j))
          * (Nat.choose (p + 1) j : ℚ) * ((j : ℚ) ^ 0))
          = 0 := by
        have hap := add_pow (1 : ℚ) (-1) (p + 1)
        rw [show (1 : ℚ) + -1 = 0 by ring,
          zero_pow (by omega : p + 1 ≠ 0)] at hap
        rw [show p + 1 + 1 = p + 2 from by omega] at hap
        have hconv : (∑ j ∈ Finset.range (p + 2), ((-1 : ℚ) ^ (p + 1 - j))
            * (Nat.choose (p + 1) j : ℚ) * ((j : ℚ) ^ 0))
            = (∑ m ∈ Finset.range (p + 2), (1 : ℚ) ^ m * (-1) ^ (p + 1 - m)
              * ((Nat.choose (p + 1) m : ℕ) : ℚ)) := by
          apply Finset.sum_congr rfl
          intro j _
          simp [pow_zero]
        rw [hconv, ← hap]
      rw [hR, Nat.stirlingSecond_zero_succ]
      norm_num
    | succ i ih2 =>
      have rs := Rstep p i
      rw [ih2, ih i] at rs
      rw [rs]
      have Pnorm : ((((p + 1 : ℕ))) : ℚ) = ((p : ℚ) + 1) := by
        push_cast
        ring
      rw [Pnorm]
      have ssQ : ((Nat.stirlingSecond (i + 1) (p + 1) : ℕ) : ℚ)
          = ((p : ℚ) + 1) * (Nat.stirlingSecond i (p + 1) : ℚ)
            + (Nat.stirlingSecond i p : ℚ) := by
        exact_mod_cast Nat.stirlingSecond_succ_succ i p
      have fs : (Nat.factorial (p + 1) : ℚ)
          = ((p : ℚ) + 1) * (Nat.factorial p : ℚ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      linear_combination (-(Nat.factorial (p + 1) : ℚ)) * ssQ
        - (Nat.stirlingSecond i p : ℚ) * fs

/-- The full alternating binomial row sum vanishes (for `p ≥ 1`). -/
private theorem alt_sum_zero (p : ℕ) (hp : 1 ≤ p) :
    (∑ j ∈ Finset.range (p + 1), ((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)) = 0 := by
  have hap := add_pow (1 : ℚ) (-1) p
  rw [show (1 : ℚ) + -1 = 0 by ring, zero_pow (by omega : p ≠ 0)] at hap
  have hconv : (∑ j ∈ Finset.range (p + 1), ((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
      = (∑ m ∈ Finset.range (p + 1), (1 : ℚ) ^ m * (-1) ^ (p - m)
        * (Nat.choose p m : ℚ)) := by
    apply Finset.sum_congr rfl
    intro j _
    rw [one_pow, one_mul]
  rw [hconv, ← hap]

/-- Partial alternating binomial row sum. -/
private theorem alt_sum_Ico (p : ℕ) (hp : 1 ≤ p) : ∀ l, l ≤ p →
    (∑ j ∈ Finset.Ico (l + 1) (p + 1), ((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
    = ((-1 : ℚ) ^ (p + 1 + l)) * (Nat.choose (p - 1) l : ℚ) := by
  have hev : ∀ l : ℕ, ((-1 : ℚ) ^ (2 * l + 2)) = 1 :=
    fun l => Even.neg_one_pow ⟨l + 1, by ring⟩
  have key : ∀ k l : ℕ, l + k = p →
      (∑ j ∈ Finset.Ico (l + 1) (p + 1), ((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
      = ((-1 : ℚ) ^ (p + 1 + l)) * (Nat.choose (p - 1) l : ℚ) := by
    intro k
    induction k with
    | zero =>
      intro l hl
      have hlp : l = p := by omega
      rw [hlp, Finset.Ico_self, Finset.sum_empty]
      have hz : (Nat.choose (p - 1) p : ℚ) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, mul_zero]
    | succ k ih =>
      intro l hl
      have hlk : (l + 1) + k = p := by omega
      have hlp : l < p := by omega
      have ihl := ih (l + 1) hlk
      have hmem : l + 1 ∉ Finset.Ico (l + 1 + 1) (p + 1) := by
        simp only [Finset.mem_Ico]
        omega
      have hsplit : Finset.Ico (l + 1) (p + 1)
          = insert (l + 1) (Finset.Ico (l + 1 + 1) (p + 1)) := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_Ico]
        omega
      rw [hsplit, Finset.sum_insert hmem, ihl]
      have hA : ((-1 : ℚ) ^ (p - (l + 1))) = (-1) ^ (p + 1 + l) := by
        have e : p + 1 + l = (p - (l + 1)) + (2 * l + 2) := by omega
        rw [e, pow_add, hev, mul_one]
      have hB : ((-1 : ℚ) ^ (p + 1 + (l + 1))) = -(-1) ^ (p + 1 + l) := by
        have e : p + 1 + (l + 1) = (p + 1 + l) + 1 := by omega
        rw [e, pow_succ]
        ring
      have hP : (Nat.choose p (l + 1) : ℚ)
          = (Nat.choose (p - 1) l : ℚ) + (Nat.choose (p - 1) (l + 1) : ℚ) := by
        have h := Nat.choose_succ_succ (p - 1) l
        rw [show (p - 1).succ = p from by omega, show l.succ = l + 1 from rfl] at h
        exact_mod_cast h
      rw [hA, hB, hP]
      ring
  intro l hl
  exact key (p - l) l (by omega)

/-- Bernoulli polynomial evaluation as an explicit sum. -/
private theorem bern_eval (n : ℕ) (q : ℚ) :
    Polynomial.eval q (Polynomial.bernoulli n)
    = ∑ i ∈ Finset.range (n + 1), bernoulli (n - i) * (Nat.choose n i : ℚ) * q ^ i := by
  rw [Polynomial.bernoulli_def, Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Polynomial.eval_monomial]

/-- Faulhaber at naturals, via Bernoulli polynomials. -/
private theorem bern_faulhaber (n j : ℕ) (hn : 1 ≤ n) :
    Polynomial.eval (j : ℚ) (Polynomial.bernoulli n)
    = bernoulli n + (n : ℚ) * ∑ l ∈ Finset.range j, ((l : ℚ) ^ (n - 1)) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have h := Polynomial.bernoulli_succ_eval j q
  have e1 : q.succ - 1 = q := by omega
  have hc : ((((q.succ : ℕ))) : ℚ) = ((q : ℚ) + 1) := by push_cast; ring
  rw [e1]
  rw [hc]
  exact h

/-- Swap a triangular double sum to an `Ico` double sum. -/
private theorem swap_range_Ico (p : ℕ) (G : ℕ → ℕ → ℚ) :
    (∑ j ∈ Finset.range (p + 1), ∑ l ∈ Finset.range j, G j l)
    = ∑ l ∈ Finset.range (p + 1), ∑ j ∈ Finset.Ico (l + 1) (p + 1), G j l := by
  have e1 : (∑ j ∈ Finset.range (p + 1), ∑ l ∈ Finset.range j, G j l)
      = ∑ j ∈ Finset.range (p + 1), ∑ l ∈ Finset.range (p + 1),
        (if l < j then G j l else 0) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjle : j ≤ p := by
      have := Finset.mem_range.mp hj
      omega
    have hset : (Finset.range (p + 1)).filter (fun l => l < j) = Finset.range j := by
      ext l
      simp only [Finset.mem_filter, Finset.mem_range]
      constructor
      · intro h
        exact h.2
      · intro h
        exact ⟨by omega, h⟩
    rw [← Finset.sum_filter, hset]
  rw [e1, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [← Finset.sum_filter]
  have hset2 : (Finset.range (p + 1)).filter (fun j => l < j)
      = Finset.Ico (l + 1) (p + 1) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨by omega, h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by omega⟩
  rw [hset2]

/-- Sign alignment for the explicit formula application. -/
private theorem neg_one_pow_add (p l : ℕ) (hp : 1 ≤ p) (h : l ≤ p - 1) :
    ((-1 : ℚ) ^ (p + 1 + l)) = (-1) ^ ((p - 1) - l) := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
  have hpk : p = (l + k) + 1 := by
    rw [← hk]
    exact (Nat.sub_add_cancel hp).symm
  have e : p + 1 + l = ((p - 1) - l) + (2 * l + 2) := by
    rw [hk, Nat.add_sub_cancel_left, hpk]
    ring
  have hev : ((-1 : ℚ) ^ (2 * l + 2)) = 1 := Even.neg_one_pow ⟨l + 1, by ring⟩
  rw [e, pow_add, hev, mul_one]

/-- Core Bernoulli–Stirling identity. -/
private theorem star (n p : ℕ) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℚ) * bernoulli (n - i)
      * (Nat.stirlingSecond i p : ℚ))
    = (n : ℚ) * (Nat.stirlingSecond (n - 1) (p - 1) : ℚ) / (p : ℚ) := by
  have hpf : (Nat.factorial p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero p)
  have hp0 : (p : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpm : (Nat.factorial (p - 1) : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have hfact : (Nat.factorial p : ℚ) = (p : ℚ) * (Nat.factorial (p - 1) : ℚ) := by
    have e : p = (p - 1) + 1 := by omega
    rw [e, Nat.factorial_succ]
    push_cast
    ring
  have perI : ∀ i ∈ Finset.range (n + 1),
      (Nat.choose n i : ℚ) * bernoulli (n - i) * (Nat.stirlingSecond i p : ℚ)
      = (Nat.factorial p : ℚ)⁻¹ * (∑ j ∈ Finset.range (p + 1),
        (Nat.choose n i : ℚ) * bernoulli (n - i) * (((-1 : ℚ) ^ (p - j))
          * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i))) := by
    intro i _
    have hex := stirling_explicit p i
    have hS : (Nat.stirlingSecond i p : ℚ)
        = (Nat.factorial p : ℚ)⁻¹ * (∑ j ∈ Finset.range (p + 1), ((-1 : ℚ) ^ (p - j))
          * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i)) := by
      rw [hex, inv_mul_cancel_left₀ hpf]
    have hdistr : ((Nat.choose n i : ℚ) * bernoulli (n - i))
          * (∑ j ∈ Finset.range (p + 1), ((-1 : ℚ) ^ (p - j))
            * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i))
        = (∑ j ∈ Finset.range (p + 1), (Nat.choose n i : ℚ) * bernoulli (n - i)
          * (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i))) :=
      Finset.mul_sum _ _ _
    linear_combination ((Nat.choose n i : ℚ) * bernoulli (n - i)) * hS
      + (Nat.factorial p : ℚ)⁻¹ * hdistr
  have stepA : (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℚ) * bernoulli (n - i)
        * (Nat.stirlingSecond i p : ℚ))
      = (Nat.factorial p : ℚ)⁻¹ * (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (p + 1),
        (Nat.choose n i : ℚ) * bernoulli (n - i) * (((-1 : ℚ) ^ (p - j))
          * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i))) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i hi => perI i hi)
  have inner : ∀ j ∈ Finset.range (p + 1),
      (∑ i ∈ Finset.range (n + 1), (Nat.choose n i : ℚ) * bernoulli (n - i)
        * (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i)))
      = (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
        * (Polynomial.eval (j : ℚ) (Polynomial.bernoulli n)) := by
    intro j _
    have be := bern_eval n (j : ℚ)
    rw [be, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have stepB : (∑ i ∈ Finset.range (n + 1), ∑ j ∈ Finset.range (p + 1),
        (Nat.choose n i : ℚ) * bernoulli (n - i) * (((-1 : ℚ) ^ (p - j))
          * (Nat.choose p j : ℚ) * ((j : ℚ) ^ i)))
      = ∑ j ∈ Finset.range (p + 1), (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
        * (Polynomial.eval (j : ℚ) (Polynomial.bernoulli n)) := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun j hj => inner j hj)
  have perJ : ∀ j ∈ Finset.range (p + 1),
      (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
        * (Polynomial.eval (j : ℚ) (Polynomial.bernoulli n))
      = (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)) * bernoulli n
        + (n : ℚ) * (∑ l ∈ Finset.range j, (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
          * ((l : ℚ) ^ (n - 1))) := by
    intro j _
    have bf := bern_faulhaber n j hn
    have hdistr2 : (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
          * (∑ l ∈ Finset.range j, ((l : ℚ) ^ (n - 1)))
        = (∑ l ∈ Finset.range j, (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
          * ((l : ℚ) ^ (n - 1))) :=
      Finset.mul_sum _ _ _
    linear_combination (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)) * bf
      + (n : ℚ) * hdistr2
  have stepC : (∑ j ∈ Finset.range (p + 1), (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
        * (Polynomial.eval (j : ℚ) (Polynomial.bernoulli n)))
      = (∑ j ∈ Finset.range (p + 1), (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)))
        * bernoulli n
        + (n : ℚ) * (∑ j ∈ Finset.range (p + 1), ∑ l ∈ Finset.range j,
          (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)) * ((l : ℚ) ^ (n - 1))) := by
    calc (∑ j ∈ Finset.range (p + 1), (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
            * (Polynomial.eval (j : ℚ) (Polynomial.bernoulli n)))
        = (∑ j ∈ Finset.range (p + 1), (((((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
            * bernoulli n)
          + (n : ℚ) * (∑ l ∈ Finset.range j, (((-1 : ℚ) ^ (p - j))
            * (Nat.choose p j : ℚ)) * ((l : ℚ) ^ (n - 1))))) :=
          Finset.sum_congr rfl (fun j hj => perJ j hj)
      _ = (∑ j ∈ Finset.range (p + 1), (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
            * bernoulli n)
          + (∑ j ∈ Finset.range (p + 1), (n : ℚ) * (∑ l ∈ Finset.range j,
            (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)) * ((l : ℚ) ^ (n - 1)))) :=
          Finset.sum_add_distrib
      _ = _ := by simp only [Finset.sum_mul, Finset.mul_sum]
  have stepD : (∑ j ∈ Finset.range (p + 1), (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)))
        * bernoulli n = 0 := by
    rw [alt_sum_zero p hp, zero_mul]
  have stepE : (∑ j ∈ Finset.range (p + 1), ∑ l ∈ Finset.range j,
        (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ)) * ((l : ℚ) ^ (n - 1)))
      = ∑ l ∈ Finset.range (p + 1), ((l : ℚ) ^ (n - 1))
        * (((-1 : ℚ) ^ (p + 1 + l)) * (Nat.choose (p - 1) l : ℚ)) := by
    rw [swap_range_Ico _ (fun j l => (((-1 : ℚ) ^ (p - j)) * (Nat.choose p j : ℚ))
      * ((l : ℚ) ^ (n - 1)))]
    apply Finset.sum_congr rfl
    intro l hl
    have hle : l ≤ p := by
      have := Finset.mem_range.mp hl
      omega
    have hI := alt_sum_Ico p hp l hle
    rw [← Finset.sum_mul, hI]
    ring
  have stepF : (∑ l ∈ Finset.range (p + 1), ((l : ℚ) ^ (n - 1))
        * (((-1 : ℚ) ^ (p + 1 + l)) * (Nat.choose (p - 1) l : ℚ)))
      = (Nat.factorial (p - 1) : ℚ) * (Nat.stirlingSecond (n - 1) (p - 1) : ℚ) := by
    have hexpl := stirling_explicit (p - 1) (n - 1)
    rw [show (p - 1) + 1 = p from by omega] at hexpl
    have peel : (∑ l ∈ Finset.range (p + 1), ((l : ℚ) ^ (n - 1))
          * (((-1 : ℚ) ^ (p + 1 + l)) * (Nat.choose (p - 1) l : ℚ)))
        = ∑ l ∈ Finset.range p, ((l : ℚ) ^ (n - 1))
          * (((-1 : ℚ) ^ (p + 1 + l)) * (Nat.choose (p - 1) l : ℚ)) := by
      rw [Finset.sum_range_succ]
      have hz : (Nat.choose (p - 1) p : ℚ) = 0 := by
        exact_mod_cast Nat.choose_eq_zero_of_lt (by omega)
      rw [hz, mul_zero, mul_zero, add_zero]
    rw [peel, ← hexpl]
    apply Finset.sum_congr rfl
    intro l hl
    have hle : l < p := by
      have := Finset.mem_range.mp hl
      omega
    have hsgn := neg_one_pow_add p l hp (by omega)
    rw [hsgn]
    ring
  rw [stepA, stepB, stepC, stepD, zero_add, stepE, stepF, hfact]
  have hne : (p : ℚ) * (Nat.factorial (p - 1) : ℚ) ≠ 0 := mul_ne_zero hp0 hpm
  field_simp

/-- Helper: `C(n+1,k+1)/(n+1) = C(n,k)/(k+1)` over ℚ. -/
private theorem choose_div (n k : ℕ) :
    (Nat.choose (n + 1) (k + 1) : ℚ) / ((n : ℚ) + 1)
    = (Nat.choose n k : ℚ) / ((k : ℚ) + 1) := by
  by_cases hkn : k ≤ n
  · have h1 : k + 1 ≤ n + 1 := by omega
    have e1 := Nat.choose_mul_factorial_mul_factorial h1
    have e2 := Nat.choose_mul_factorial_mul_factorial hkn
    rw [show (n + 1) - (k + 1) = n - k from by omega] at e1
    have c1 : (Nat.choose (n + 1) (k + 1) : ℚ) * (Nat.factorial (k + 1) : ℚ)
        * (Nat.factorial (n - k) : ℚ) = (Nat.factorial (n + 1) : ℚ) := by
      exact_mod_cast e1
    have c2 : (Nat.choose n k : ℚ) * (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ)
        = (Nat.factorial n : ℚ) := by
      exact_mod_cast e2
    have fk : (Nat.factorial (k + 1) : ℚ) = ((k : ℚ) + 1) * (Nat.factorial k : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have fn : (Nat.factorial (n + 1) : ℚ) = ((n : ℚ) + 1) * (Nat.factorial n : ℚ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hk1 : ((k : ℚ) + 1) ≠ 0 := by
      have hkk : k + 1 ≠ 0 := Nat.succ_ne_zero k
      exact_mod_cast hkk
    have hn1 : ((n : ℚ) + 1) ≠ 0 := by
      have hnn : n + 1 ≠ 0 := Nat.succ_ne_zero n
      exact_mod_cast hnn
    have hkf : (Nat.factorial k : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero k)
    have hnkf : (Nat.factorial (n - k) : ℚ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
    have c1' : (Nat.choose (n + 1) (k + 1) : ℚ) * (((k : ℚ) + 1) * (Nat.factorial k : ℚ))
        * (Nat.factorial (n - k) : ℚ) = ((n : ℚ) + 1) * (Nat.factorial n : ℚ) := by
      rw [← fk, ← fn]
      exact c1
    have key : ((Nat.choose (n + 1) (k + 1) : ℚ) * ((k : ℚ) + 1)
        - (Nat.choose n k : ℚ) * ((n : ℚ) + 1))
        * ((Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ)) = 0 := by
      linear_combination c1' - ((n : ℚ) + 1) * c2
    have hfac : (Nat.factorial k : ℚ) * (Nat.factorial (n - k) : ℚ) ≠ 0 :=
      mul_ne_zero hkf hnkf
    have hgoal : (Nat.choose (n + 1) (k + 1) : ℚ) * ((k : ℚ) + 1)
        - (Nat.choose n k : ℚ) * ((n : ℚ) + 1) = 0 :=
      (mul_eq_zero.mp key).resolve_right hfac
    rw [div_eq_div_iff hn1 hk1]
    linear_combination hgoal
  · push Not at hkn
    have hz1 : (Nat.choose n k : ℚ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt hkn
    have hz2 : (Nat.choose (n + 1) (k + 1) : ℚ) = 0 := by
      exact_mod_cast Nat.choose_eq_zero_of_lt (by omega : n + 1 < k + 1)
    rw [hz1, hz2]
    simp

private theorem exp_summ (x : ℂ) : Summable (fun n : ℕ => x ^ n / (Nat.factorial n : ℂ)) :=
  NormedSpace.expSeries_div_summable x

private theorem exp_val (x : ℂ) : (∑' n : ℕ, x ^ n / (Nat.factorial n : ℂ)) = Complex.exp x := by
  have h := NormedSpace.exp_eq_tsum_div (𝔸 := ℂ)
  have hx : NormedSpace.exp x = ∑' n : ℕ, x ^ n / (Nat.factorial n : ℂ) := congrFun h x
  rw [← Complex.exp_eq_exp_ℂ] at hx
  exact hx.symm

/-- Shifted exponential series: summability and value. -/
private theorem shift_exp (k : ℕ) (x : ℂ) (G : ℕ → ℂ)
    (hG : ∀ i, G i = (if k ≤ i then x ^ (i - k) / (Nat.factorial (i - k) : ℂ) else 0)) :
    Summable G ∧ ∑' i, G i = Complex.exp x := by
  have hex := exp_summ x
  have hpoint : ∀ n : ℕ, G (n + k) = x ^ n / (Nat.factorial n : ℂ) := by
    intro n
    rw [hG, ite_eq_left (Nat.le_add_left k n), Nat.add_sub_cancel]
  have htailS : Summable (fun n : ℕ => G (n + k)) :=
    (summable_congr hpoint).mpr hex
  have hsG : Summable G := (summable_nat_add_iff k).mp htailS
  refine ⟨hsG, ?_⟩
  have hshift := Summable.sum_add_tsum_nat_add k hsG
  have hzero : (∑ i ∈ Finset.range k, G i) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hni : ¬ k ≤ i := by
      have := Finset.mem_range.mp hi
      omega
    rw [hG, ite_eq_right hni]
  have htailV : (∑' i : ℕ, G (i + k)) = Complex.exp x := by
    rw [← exp_val x]
    exact tsum_congr hpoint
  rw [hzero, zero_add, htailV] at hshift
  exact hshift.symm

/-- Dobinski-type formula. -/
private theorem dobinski (K : ℕ) (x : ℂ) :
    Summable (fun i : ℕ => (i : ℂ) ^ K * x ^ i / (Nat.factorial i : ℂ))
    ∧ (∑' i : ℕ, (i : ℂ) ^ K * x ^ i / (Nat.factorial i : ℂ))
      = Complex.exp x * (∑ a ∈ Finset.range (K + 1),
        (Nat.stirlingSecond K a : ℂ) * x ^ a) := by
  have hpow : ∀ i : ℕ, ((i : ℂ) ^ K)
      = ∑ a ∈ Finset.range (K + 1), (Nat.stirlingSecond K a : ℂ)
        * ((i.descFactorial a : ℕ) : ℂ) := by
    intro i
    exact_mod_cast Nat.pow_eq_sum_stirlingSecond_mul_descFactorial i K
  have perTerm : ∀ a ∈ Finset.range (K + 1), ∀ i : ℕ,
      (Nat.stirlingSecond K a : ℂ) * ((i.descFactorial a : ℕ) : ℂ)
        * (x ^ i / (Nat.factorial i : ℂ))
      = (Nat.stirlingSecond K a : ℂ) * x ^ a
        * (if a ≤ i then x ^ (i - a) / (Nat.factorial (i - a) : ℂ) else 0) := by
    intro a _ i
    by_cases ha : a ≤ i
    · have hdvd : Nat.factorial (i - a) ∣ Nat.factorial i :=
        Nat.factorial_dvd_factorial (Nat.sub_le i a)
      have hd : ((i.descFactorial a : ℕ) : ℂ)
          = (Nat.factorial i : ℂ) / (Nat.factorial (i - a) : ℂ) := by
        have h := Nat.descFactorial_eq_div ha
        have h2 : (Nat.factorial (i - a) : ℂ) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
        rw [h]
        exact Nat.cast_div hdvd h2
      have hxi : x ^ i = x ^ a * x ^ (i - a) :=
        calc x ^ i = x ^ (a + (i - a)) := by
              rw [show a + (i - a) = i from by omega]
          _ = x ^ a * x ^ (i - a) := pow_add x a (i - a)
      have h1 : (Nat.factorial i : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero i)
      have h2 : (Nat.factorial (i - a) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
      rw [ite_eq_left ha, hd, hxi]
      field_simp
    · have hlt : i < a := by omega
      have hd : i.descFactorial a = 0 :=
        Nat.descFactorial_eq_zero_iff_lt.mpr hlt
      rw [hd, Nat.cast_zero, mul_zero, zero_mul, ite_eq_right ha, mul_zero]
  have hsumA : ∀ a ∈ Finset.range (K + 1),
      Summable (fun i : ℕ => (Nat.stirlingSecond K a : ℂ)
        * ((i.descFactorial a : ℕ) : ℂ) * (x ^ i / (Nat.factorial i : ℂ))) := by
    intro a ha
    have hG := ((shift_exp a x (fun i : ℕ => if a ≤ i
      then x ^ (i - a) / (Nat.factorial (i - a) : ℂ) else 0)) (fun i => rfl)).1
    have hmul := hG.mul_left ((Nat.stirlingSecond K a : ℂ) * x ^ a)
    apply (summable_congr _).mpr hmul
    intro i
    exact perTerm a ha i
  have hvalA : ∀ a ∈ Finset.range (K + 1),
      (∑' i : ℕ, (Nat.stirlingSecond K a : ℂ) * ((i.descFactorial a : ℕ) : ℂ)
        * (x ^ i / (Nat.factorial i : ℂ)))
      = (Nat.stirlingSecond K a : ℂ) * x ^ a * Complex.exp x := by
    intro a ha
    have hGv := ((shift_exp a x (fun i : ℕ => if a ≤ i
      then x ^ (i - a) / (Nat.factorial (i - a) : ℂ) else 0)) (fun i => rfl)).2
    calc (∑' i : ℕ, (Nat.stirlingSecond K a : ℂ) * ((i.descFactorial a : ℕ) : ℂ)
            * (x ^ i / (Nat.factorial i : ℂ)))
        = (∑' i : ℕ, ((Nat.stirlingSecond K a : ℂ) * x ^ a)
            * (if a ≤ i then x ^ (i - a) / (Nat.factorial (i - a) : ℂ) else 0)) :=
          tsum_congr (fun i => perTerm a ha i)
      _ = ((Nat.stirlingSecond K a : ℂ) * x ^ a)
            * (∑' i : ℕ, (if a ≤ i then x ^ (i - a) / (Nat.factorial (i - a) : ℂ)
              else 0)) := tsum_mul_left
      _ = (Nat.stirlingSecond K a : ℂ) * x ^ a * Complex.exp x := by rw [hGv]
  have hinter : (∑' i : ℕ, ∑ a ∈ Finset.range (K + 1),
        (Nat.stirlingSecond K a : ℂ) * ((i.descFactorial a : ℕ) : ℂ)
          * (x ^ i / (Nat.factorial i : ℂ)))
      = ∑ a ∈ Finset.range (K + 1), ∑' i : ℕ,
        (Nat.stirlingSecond K a : ℂ) * ((i.descFactorial a : ℕ) : ℂ)
          * (x ^ i / (Nat.factorial i : ℂ)) :=
    Summable.tsum_finsetSum (fun a ha => hsumA a ha)
  have hexp : (∀ i : ℕ, (i : ℂ) ^ K * x ^ i / (Nat.factorial i : ℂ)
      = ∑ a ∈ Finset.range (K + 1), (Nat.stirlingSecond K a : ℂ)
        * ((i.descFactorial a : ℕ) : ℂ) * (x ^ i / (Nat.factorial i : ℂ))) := by
    intro i
    rw [hpow i, Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro a _
    ring
  refine ⟨(summable_congr hexp).mpr
    (summable_sum (fun a ha => hsumA a ha)), ?_⟩
  calc (∑' i : ℕ, (i : ℂ) ^ K * x ^ i / (Nat.factorial i : ℂ))
      = (∑' i : ℕ, ∑ a ∈ Finset.range (K + 1), (Nat.stirlingSecond K a : ℂ)
        * ((i.descFactorial a : ℕ) : ℂ) * (x ^ i / (Nat.factorial i : ℂ))) :=
        tsum_congr hexp
    _ = ∑ a ∈ Finset.range (K + 1), ∑' i : ℕ, (Nat.stirlingSecond K a : ℂ)
        * ((i.descFactorial a : ℕ) : ℂ) * (x ^ i / (Nat.factorial i : ℂ)) := hinter
    _ = ∑ a ∈ Finset.range (K + 1), (Nat.stirlingSecond K a : ℂ) * x ^ a
        * Complex.exp x :=
        Finset.sum_congr rfl (fun a ha => hvalA a ha)
    _ = Complex.exp x * (∑ a ∈ Finset.range (K + 1),
        (Nat.stirlingSecond K a : ℂ) * x ^ a) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro a _
        ring

private theorem f_touchard (N : ℕ) (x : ℂ) (h : -1 ≤ (N : ℤ)) :
    f ⟨(N : ℤ), h⟩ x = ∑ k ∈ Finset.range (N + 1 + 1),
      (Nat.stirlingSecond (N + 1) k : ℂ) * x ^ k := by
  rw [f_natCast, generalizedBellGenerating]
  simp only [zero_add, one_mul]
  show Complex.exp (-x) * (∑' j : ℕ, ((j + 1 : ℕ) : ℂ) ^ N * x ^ (j + 1)
      / (Nat.factorial j : ℂ))
    = ∑ k ∈ Finset.range (N + 1 + 1), (Nat.stirlingSecond (N + 1) k : ℂ) * x ^ k
  have hH := dobinski (N + 1) x
  have hj : ∀ j : ℕ, ((j + 1 : ℕ) : ℂ) ^ N * x ^ (j + 1) / (Nat.factorial j : ℂ)
      = ((j + 1 : ℕ) : ℂ) ^ (N + 1) * x ^ (j + 1) / (Nat.factorial (j + 1) : ℂ) := by
    intro j
    have hf : (Nat.factorial (j + 1) : ℂ)
        = (((j + 1 : ℕ)) : ℂ) * (Nat.factorial j : ℂ) := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have h1 : (Nat.factorial j : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j)
    have h2 : ((((j + 1 : ℕ))) : ℂ) ≠ 0 := by
      exact_mod_cast Nat.succ_ne_zero j
    rw [hf]
    field_simp
    ring
  have hH0 : ((0 : ℕ) : ℂ) ^ (N + 1) * x ^ (0 : ℕ) / (Nat.factorial 0 : ℂ) = 0 := by
    simp only [Nat.cast_zero, zero_pow (show N + 1 ≠ 0 by omega), zero_mul, zero_div]
  have hsum1 : (∑ i ∈ Finset.range 1, (i : ℂ) ^ (N + 1) * x ^ i
      / (Nat.factorial i : ℂ)) = 0 := by
    rw [Finset.sum_range_one]
    exact hH0
  have hshift := Summable.sum_add_tsum_nat_add 1 hH.1
  rw [hsum1, zero_add] at hshift
  have hshift3 : (∑' i : ℕ, ((i + 1 : ℕ) : ℂ) ^ (N + 1) * x ^ (i + 1)
      / (Nat.factorial (i + 1) : ℂ))
      = (∑' i : ℕ, (i : ℂ) ^ (N + 1) * x ^ i / (Nat.factorial i : ℂ)) := hshift
  have hseries : (∑' j : ℕ, ((j + 1 : ℕ) : ℂ) ^ N * x ^ (j + 1)
      / (Nat.factorial j : ℂ))
      = (∑' i : ℕ, ((i + 1 : ℕ) : ℂ) ^ (N + 1) * x ^ (i + 1)
        / (Nat.factorial (i + 1) : ℂ)) :=
    tsum_congr hj
  rw [hseries, hshift3, hH.2, Complex.exp_neg, inv_mul_cancel_left₀
    (Complex.exp_ne_zero x)]

private theorem integral_pow_complex (a : ℕ) :
    (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), ((t : ℂ) ^ a)) = (1 : ℂ) / (((a : ℂ) + 1)) := by
  have hfun : (fun t : ℝ => ((t : ℂ) ^ a)) = (fun t => (((t ^ a : ℝ)) : ℂ)) := by
    funext t
    rw [Complex.ofReal_pow]
  rw [hfun, intervalIntegral.integral_ofReal, integral_pow]
  have h0 : (0 : ℝ) ^ (a + 1) = 0 := zero_pow (Nat.succ_ne_zero a)
  have h1 : (1 : ℝ) ^ (a + 1) = 1 := one_pow _
  rw [h0, h1, sub_zero]
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_add,
    Complex.ofReal_natCast, Complex.ofReal_one]

/-- Bracket coefficient identity over ℚ. -/
private theorem bracketQ (m q : ℕ) (hq : 1 ≤ q) :
    (∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℚ) * bernoulli (m - k)
      * (Nat.stirlingSecond (k + 1) q : ℚ) / (((k : ℚ) + 1)))
    = (Nat.stirlingSecond m (q - 1) : ℚ) / (q : ℚ) := by
  by_cases hm : m = 0
  · subst hm
    rw [Finset.sum_range_one]
    simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.zero_sub]
    by_cases hq1 : q = 1
    · subst hq1
      simp only [Nat.cast_one, div_one, Nat.sub_self]
      rw [Nat.stirlingSecond_self, Nat.stirlingSecond_self]
      simp [bernoulli_zero]
    · have hS1 : Nat.stirlingSecond 1 q = 0 := by
        apply Nat.stirlingSecond_eq_zero_of_lt
        omega
      have hS0 : Nat.stirlingSecond 0 (q - 1) = 0 := by
        apply Nat.stirlingSecond_eq_zero_of_lt
        omega
      rw [hS1, hS0]
      simp [bernoulli_zero]
  · have hm1' : 1 ≤ m + 1 := by omega
    have per : ∀ k ∈ Finset.range (m + 1),
        (Nat.choose m k : ℚ) * bernoulli (m - k)
          * (Nat.stirlingSecond (k + 1) q : ℚ) / (((k : ℚ) + 1))
        = (((m : ℚ) + 1))⁻¹ * ((Nat.choose (m + 1) (k + 1) : ℚ)
          * bernoulli ((m + 1) - (k + 1)) * (Nat.stirlingSecond (k + 1) q : ℚ)) := by
      intro k hk
      have hsub : (m + 1) - (k + 1) = m - k := by omega
      rw [hsub]
      have cd2 : (Nat.choose m k : ℚ) / (((k : ℚ) + 1))
          = (Nat.choose (m + 1) (k + 1) : ℚ) / (((m : ℚ) + 1)) :=
        (choose_div m k).symm
      calc (Nat.choose m k : ℚ) * bernoulli (m - k)
            * (Nat.stirlingSecond (k + 1) q : ℚ) / (((k : ℚ) + 1))
          = ((Nat.choose m k : ℚ) / (((k : ℚ) + 1))) * bernoulli (m - k)
            * (Nat.stirlingSecond (k + 1) q : ℚ) := by ring
        _ = ((Nat.choose (m + 1) (k + 1) : ℚ) / (((m : ℚ) + 1))) * bernoulli (m - k)
            * (Nat.stirlingSecond (k + 1) q : ℚ) := by rw [cd2]
        _ = (((m : ℚ) + 1))⁻¹ * ((Nat.choose (m + 1) (k + 1) : ℚ)
            * bernoulli (m - k) * (Nat.stirlingSecond (k + 1) q : ℚ)) := by ring
    rw [Finset.sum_congr rfl (fun k hk => per k hk), ← Finset.mul_sum]
    have hreindex : (∑ k ∈ Finset.range (m + 1), (Nat.choose (m + 1) (k + 1) : ℚ)
          * bernoulli ((m + 1) - (k + 1)) * (Nat.stirlingSecond (k + 1) q : ℚ))
        = ∑ i ∈ Finset.range (m + 2), (Nat.choose (m + 1) i : ℚ)
          * bernoulli ((m + 1) - i) * (Nat.stirlingSecond i q : ℚ) := by
      have hshift := Finset.sum_range_succ' (fun i => (Nat.choose (m + 1) i : ℚ)
        * bernoulli ((m + 1) - i) * (Nat.stirlingSecond i q : ℚ)) (m + 1)
      have hG0 : (Nat.choose (m + 1) 0 : ℚ)
          * bernoulli ((m + 1) - 0) * (Nat.stirlingSecond 0 q : ℚ) = 0 := by
        have hSq : Nat.stirlingSecond 0 q = 0 :=
          Nat.stirlingSecond_eq_zero_of_lt (by omega)
        rw [hSq, Nat.cast_zero, mul_zero]
      rw [hG0, add_zero] at hshift
      exact hshift.symm
    rw [hreindex, star (m + 1) q hm1' hq]
    have hsub1 : (m + 1) - 1 = m := by omega
    rw [hsub1]
    have hcast : (((m + 1 : ℕ)) : ℚ) = ((m : ℚ) + 1) := by push_cast; ring
    rw [hcast]
    field_simp

private theorem bracketC (m q : ℕ) (hq : 1 ≤ q) :
    (∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℂ) * (((bernoulli (m - k) : ℚ)) : ℂ)
      * (Nat.stirlingSecond (k + 1) q : ℂ) / (((k : ℂ) + 1)))
    = (Nat.stirlingSecond m (q - 1) : ℂ) / (q : ℂ) := by
  have hQ := bracketQ m q hq
  have hQc := congrArg (Rat.cast : ℚ → ℂ) hQ
  simp only [Rat.cast_sum, Rat.cast_div, Rat.cast_mul, Rat.cast_natCast,
    Rat.cast_add, Rat.cast_one] at hQc
  exact hQc

/-- Extend Touchard sum range using vanishing Stirling numbers. -/
private theorem extend_range (k m : ℕ) (hkm : k ≤ m) (x : ℂ) :
    (∑ a ∈ Finset.range (k + 1 + 1), (Nat.stirlingSecond (k + 1) a : ℂ) * x ^ a)
    = ∑ a ∈ Finset.range (m + 2), (Nat.stirlingSecond (k + 1) a : ℂ) * x ^ a := by
  apply Finset.sum_subset (by simpa using Nat.add_le_add_right hkm 2)
  intro a ham hanot
  simp only [Finset.mem_range, not_lt] at hanot
  have hak : k + 1 < a := by omega
  have hS : Nat.stirlingSecond (k + 1) a = 0 :=
    Nat.stirlingSecond_eq_zero_of_lt hak
  rw [hS, Nat.cast_zero, zero_mul]

/-- LHS evaluation for `m = n+1`. -/
private theorem LHS_eq (n : ℕ) (x : ℂ) :
    (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), x * f ⟨((↑(n + 1) : ℤ) - 1), by omega⟩ ((↑t : ℂ) * x))
    = ∑ a ∈ Finset.range (n + 2),
        (Nat.stirlingSecond (n + 1) a : ℂ) * x ^ (a + 1) / (((a : ℂ) + 1)) := by
  have hsub : (⟨((↑(n + 1) : ℤ) - 1), by omega⟩ : {n : ℤ // -1 ≤ n}) = ⟨((↑n : ℤ)), by omega⟩ := by
    apply Subtype.ext
    push_cast
    ring
  rw [hsub]
  have hf : ∀ t : ℝ, f ⟨((↑n : ℤ)), by omega⟩ ((↑t : ℂ) * x)
      = ∑ a ∈ Finset.range (n + 2), (Nat.stirlingSecond (n + 1) a : ℂ) * ((↑t : ℂ) * x) ^ a := by
    intro t
    have h := f_touchard n ((↑t : ℂ) * x) (by omega)
    rw [show n + 1 + 1 = n + 2 from by omega] at h
    exact h
  have hint : ∀ a ∈ Finset.range (n + 2),
      IntervalIntegrable
        (fun t : ℝ => (Nat.stirlingSecond (n + 1) a : ℂ) * x ^ (a + 1) * ((t : ℂ) ^ a))
        MeasureTheory.volume (0 : ℝ) (1 : ℝ) := by
    intro a _
    apply Continuous.intervalIntegrable
    apply Continuous.mul
    · exact continuous_const
    · exact Complex.continuous_ofReal.pow a
  have hrewrite : (fun t : ℝ => x * f ⟨((↑n : ℤ)), by omega⟩ ((↑t : ℂ) * x))
      = (fun t : ℝ => ∑ a ∈ Finset.range (n + 2),
          (Nat.stirlingSecond (n + 1) a : ℂ) * x ^ (a + 1) * ((t : ℂ) ^ a)) := by
    funext t
    rw [hf t, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [mul_pow]
    ring
  rw [hrewrite, intervalIntegral.integral_finsetSum (fun a ha => hint a ha)]
  apply Finset.sum_congr rfl
  intro a _
  rw [intervalIntegral.integral_const_mul, integral_pow_complex a]
  ring

private theorem RHS_eq (m : ℕ) (x : ℂ) :
    (∑ k ∈ Finset.range (m + 1), (↑(Nat.choose m k) : ℂ) * ((((bernoulli (m - k) : ℚ))) : ℂ) *
        f ⟨↑k, neg_one_le_natCast k⟩ x / (↑(k + 1) : ℂ))
    = ∑ a ∈ Finset.range (m + 2), ((∑ k ∈ Finset.range (m + 1),
        (↑(Nat.choose m k) : ℂ) * ((((bernoulli (m - k) : ℚ))) : ℂ) *
        (Nat.stirlingSecond (k + 1) a : ℂ) / (((k : ℂ) + 1))) * x ^ a) := by
  have hcast : ∀ k : ℕ, (((k : ℂ) + 1)) = ((↑(k + 1) : ℕ) : ℂ) := by
    intro k
    push_cast
    ring
  have perK : ∀ k ∈ Finset.range (m + 1),
      (↑(Nat.choose m k) : ℂ) * ((((bernoulli (m - k) : ℚ))) : ℂ) *
        f ⟨↑k, by omega⟩ x / (↑(k + 1) : ℂ)
      = ∑ a ∈ Finset.range (m + 2), (↑(Nat.choose m k) : ℂ) * ((((bernoulli (m - k) : ℚ))) : ℂ) *
        (Nat.stirlingSecond (k + 1) a : ℂ) / (((k : ℂ) + 1)) * x ^ a := by
    intro k hk
    have hkm : k ≤ m := by
      have hmem := Finset.mem_range.mp hk
      omega
    have hf := f_touchard k x (by omega)
    have hfe : f ⟨↑k, by omega⟩ x
        = ∑ a ∈ Finset.range (m + 2), (Nat.stirlingSecond (k + 1) a : ℂ) * x ^ a := by
      rw [hf]
      exact extend_range k m hkm x
    rw [hfe, Finset.mul_sum, Finset.sum_div, hcast k]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [Finset.sum_congr rfl (fun k hk => perK k hk), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_mul]

private theorem inner_zero (m : ℕ) :
    (∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℂ) * ((((bernoulli (m - k) : ℚ))) : ℂ)
      * (Nat.stirlingSecond (k + 1) 0 : ℂ) / (((k : ℂ) + 1))) = 0 := by
  apply Finset.sum_eq_zero
  intro k _
  have hS : Nat.stirlingSecond (k + 1) 0 = 0 := Nat.stirlingSecond_succ_zero k
  rw [hS, Nat.cast_zero, mul_zero, zero_div]

private theorem coeff_match (m : ℕ) (x : ℂ) :
    (∑ a ∈ Finset.range (m + 2), ((∑ k ∈ Finset.range (m + 1),
        (↑(Nat.choose m k) : ℂ) * ((((bernoulli (m - k) : ℚ))) : ℂ) *
        (Nat.stirlingSecond (k + 1) a : ℂ) / (((k : ℂ) + 1))) * x ^ a))
    = ∑ a ∈ Finset.range (m + 1), (Nat.stirlingSecond m a : ℂ) * x ^ (a + 1) / (((a : ℂ) + 1)) := by
  have hF0 : ((∑ k ∈ Finset.range (m + 1),
        (↑(Nat.choose m k) : ℂ) * ((((bernoulli (m - k) : ℚ))) : ℂ) *
        (Nat.stirlingSecond (k + 1) 0 : ℂ) / (((k : ℂ) + 1))) * x ^ 0) = 0 := by
    rw [inner_zero m, zero_mul]
  have hshift := Finset.sum_range_succ' (fun a => ((∑ k ∈ Finset.range (m + 1),
        (↑(Nat.choose m k) : ℂ) * ((((bernoulli (m - k) : ℚ))) : ℂ) *
        (Nat.stirlingSecond (k + 1) a : ℂ) / (((k : ℂ) + 1))) * x ^ a)) (m + 1)
  rw [hF0, add_zero] at hshift
  rw [hshift]
  apply Finset.sum_congr rfl
  intro a _
  have hq : 1 ≤ a + 1 := by omega
  have hbr := bracketC m (a + 1) hq
  rw [show a + 1 - 1 = a from by omega] at hbr
  have hcast : (((a : ℂ) + 1)) = (((a + 1 : ℕ)) : ℂ) := by push_cast; ring
  rw [hbr, hcast]
  ring

private theorem zero_LHS (x : ℂ) :
    (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), x * f ⟨(((0 : ℕ) : ℤ) - 1), by omega⟩ ((↑t : ℂ) * x))
    = x := by
  have hsub : (⟨(((0 : ℕ) : ℤ) - 1), by omega⟩ : {n : ℤ // -1 ≤ n}) = ⟨(-1 : ℤ), by omega⟩ := by
    apply Subtype.ext
    simp
  rw [hsub]
  have hf : ∀ t : ℝ, f ⟨(-1 : ℤ), by omega⟩ ((↑t : ℂ) * x) = 1 := by
    intro t
    unfold f
    simp
  simp_rw [hf, mul_one]
  rw [intervalIntegral.integral_const]
  simp

private theorem zero_RHS (x : ℂ) :
    (∑ k ∈ Finset.range (0 + 1), (↑(Nat.choose 0 k) : ℂ) * (((bernoulli (0 - k) : ℚ)) : ℂ) *
        f ⟨↑k, neg_one_le_natCast k⟩ x / (↑(k + 1) : ℂ)) = x := by
  rw [Finset.sum_range_one]
  simp only [Nat.choose_self, Nat.cast_one, one_mul, Nat.zero_sub,
    zero_add, div_one] at ⊢
  have hB0 : ((((bernoulli 0 : ℚ))) : ℂ) = 1 := by
    rw [bernoulli_zero]
    simp
  rw [hB0, one_mul]
  have hf0 := f_touchard 0 x (by omega)
  rw [show (0 : ℕ) + 1 + 1 = 2 from by omega] at hf0
  rw [hf0]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.stirlingSecond_one_right, Nat.cast_one, one_mul,
    Nat.stirlingSecond_succ_zero, Nat.cast_zero, zero_mul, pow_zero, pow_one]
  simp

/-- **Ramanujan's integral formula with Bernoulli numbers.** Let $f(-1, x) = 1$ and, for natural
numbers $n$, let $f(n, x) = e^{-x} \sum_{j=0}^{\infty} (j + 1)^n x^{j+1} / j!$ for complex $x$.
Let $B_n$ be the Bernoulli numbers, with $B_1 = -1/2$. Then for every natural number $m$ and every
complex number $x$,
$$\int_0^1 x\, f(m - 1, t x)\, dt = \sum_{k=0}^{m} \binom{m}{k} B_{m-k} \frac{f(k, x)}{k + 1}.$$

Source: Berndt, Ramanujan's Notebooks Part I, Chapter 3, Section 8, Example 4 and its
    correction, printed pp. 51--52 / PDF pp. 61--62.
Proves `Wanted` entry `ramanujan_part1_ch3_section8_example4_bernoulli_integral`.
-/
theorem ramanujan_part1_ch3_section8_example4_bernoulli_integral (m : ℕ) (x : ℂ) :
    ∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ), x * f ⟨(↑m : ℤ) - 1, by omega⟩ ((↑t : ℂ) * x) =
      ∑ k ∈ Finset.range (m + 1), (↑(Nat.choose m k) : ℂ) * (↑(bernoulli (m - k)) : ℂ) *
          f ⟨↑k, by omega⟩ x / (↑(k + 1) : ℂ) := by
  cases m with
  | zero =>
    have hL := zero_LHS x
    have hR := zero_RHS x
    simp only [Nat.cast_zero] at hL hR ⊢
    rw [hL, hR]
  | succ n =>
    have hL := LHS_eq n x
    have hR := RHS_eq (n + 1) x
    have hC := coeff_match (n + 1) x
    have hgoal : (∫ (t : ℝ) in (0 : ℝ)..(1 : ℝ),
          x * f ⟨((↑(n + 1) : ℤ) - 1), by omega⟩ ((↑t : ℂ) * x))
        = (∑ k ∈ Finset.range (n + 1 + 1), (↑(Nat.choose (n + 1) k) : ℂ) *
          (((bernoulli ((n + 1) - k) : ℚ)) : ℂ) * f ⟨↑k, by omega⟩ x / (↑(k + 1) : ℂ)) := by
      rw [hL, hR, hC]
    simpa using hgoal

end Section8Example4BernoulliIntegral

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
