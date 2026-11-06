/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
public import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Choose.Dvd

@[expose] public section

namespace MetaMathlibExt

/-! # Fibonacci divisibility at `p - (5/p)`
-/

/-- Even part of `(1 + √5)^n`: `∑ k, C(n,2k) 5^k`. -/
private def evenSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n (2 * k) : ℤ) * 5 ^ k

/-- Odd part of `(1 + √5)^n`: `∑ k, C(n,2k+1) 5^k`. -/
private def oddSum (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range (n + 1), (Nat.choose n (2 * k + 1) : ℤ) * 5 ^ k

/-- Pascal's rule at an even index. -/
private lemma pascal_even (n k : ℕ) :
    Nat.choose (n + 1) (2 * (k + 1))
      = Nat.choose n (2 * k + 1) + Nat.choose n (2 * (k + 1)) := by
  have h := Nat.choose_succ_succ n (2 * k + 1)
  rw [Nat.succ_eq_add_one n, show (2 * k + 1).succ = 2 * (k + 1) from by omega] at h
  exact h

/-- Pascal's rule at an odd index. -/
private lemma pascal_odd (n k : ℕ) :
    Nat.choose (n + 1) (2 * (k + 1) + 1)
      = Nat.choose n (2 * (k + 1)) + Nat.choose n (2 * (k + 1) + 1) := by
  have h := Nat.choose_succ_succ n (2 * (k + 1))
  rw [Nat.succ_eq_add_one n, Nat.succ_eq_add_one (2 * (k + 1))] at h
  exact h

/-- First-order relation for the even part. -/
private lemma evenSum_step (n : ℕ) :
    evenSum (n + 1) = evenSum n + 5 * oddSum n := by
  have hF0 : ((Nat.choose (n + 1) (2 * 0) : ℤ) * 5 ^ (0 : ℕ)) = 1 := by simp
  have hG0 : ((Nat.choose n (2 * 0) : ℤ) * 5 ^ (0 : ℕ)) = 1 := by simp
  have hHn : ((Nat.choose n (2 * n + 1) : ℤ) * 5 ^ n) = 0 := by
    have h : Nat.choose n (2 * n + 1) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h, Nat.cast_zero, zero_mul]
  have hFn1 : ((Nat.choose (n + 1) (2 * (n + 1)) : ℤ) * 5 ^ (n + 1)) = 0 := by
    have h : Nat.choose (n + 1) (2 * (n + 1)) = 0 := Nat.choose_eq_zero_of_lt (by omega)
    rw [h, Nat.cast_zero, zero_mul]
  have key : ∀ k ∈ Finset.range n,
      ((Nat.choose (n + 1) (2 * (k + 1)) : ℤ) * 5 ^ (k + 1))
        = ((Nat.choose n (2 * (k + 1)) : ℤ) * 5 ^ (k + 1))
          + 5 * (((Nat.choose n (2 * k + 1) : ℤ)) * 5 ^ k) := by
    intro k _
    rw [pascal_even n k]
    push_cast
    ring
  have hL1 : (∑ k ∈ Finset.range (n + 1 + 1),
        ((Nat.choose (n + 1) (2 * k) : ℤ) * 5 ^ k))
      = 1 + (∑ k ∈ Finset.range n,
        ((Nat.choose (n + 1) (2 * (k + 1)) : ℤ) * 5 ^ (k + 1))) := by
    rw [Finset.sum_range_succ, hFn1, add_zero, Finset.sum_range_succ', hF0]
    exact add_comm _ _
  have hE1 : (∑ k ∈ Finset.range (n + 1), ((Nat.choose n (2 * k) : ℤ) * 5 ^ k))
      = 1 + (∑ k ∈ Finset.range n,
        ((Nat.choose n (2 * (k + 1)) : ℤ) * 5 ^ (k + 1))) := by
    rw [Finset.sum_range_succ', hG0]
    exact add_comm _ _
  have hO1 : (∑ k ∈ Finset.range (n + 1), ((Nat.choose n (2 * k + 1) : ℤ) * 5 ^ k))
      = (∑ k ∈ Finset.range n, ((Nat.choose n (2 * k + 1) : ℤ) * 5 ^ k)) := by
    rw [Finset.sum_range_succ, hHn, add_zero]
  have hsum : (∑ k ∈ Finset.range n,
        ((Nat.choose (n + 1) (2 * (k + 1)) : ℤ) * 5 ^ (k + 1)))
      = (∑ k ∈ Finset.range n, ((Nat.choose n (2 * (k + 1)) : ℤ) * 5 ^ (k + 1)))
        + (∑ k ∈ Finset.range n, 5 * (((Nat.choose n (2 * k + 1) : ℤ)) * 5 ^ k)) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl key
  unfold evenSum oddSum
  rw [hL1, hE1, hO1, Finset.mul_sum]
  linear_combination hsum

/-- First-order relation for the odd part. -/
private lemma oddSum_step (n : ℕ) :
    oddSum (n + 1) = oddSum n + evenSum n := by
  have hF0 : ((Nat.choose (n + 1) (2 * 0 + 1) : ℤ) * 5 ^ (0 : ℕ)) = (n : ℤ) + 1 := by
    simp [Nat.choose_one_right]
  have hH0 : ((Nat.choose n (2 * 0 + 1) : ℤ) * 5 ^ (0 : ℕ)) = (n : ℤ) := by
    simp [Nat.choose_one_right]
  have hG0 : ((Nat.choose n (2 * 0) : ℤ) * 5 ^ (0 : ℕ)) = 1 := by simp
  have hFn1 : ((Nat.choose (n + 1) (2 * (n + 1) + 1) : ℤ) * 5 ^ (n + 1)) = 0 := by
    have h : Nat.choose (n + 1) (2 * (n + 1) + 1) = 0 :=
      Nat.choose_eq_zero_of_lt (by omega)
    rw [h, Nat.cast_zero, zero_mul]
  have key : ∀ k ∈ Finset.range n,
      ((Nat.choose (n + 1) (2 * (k + 1) + 1) : ℤ) * 5 ^ (k + 1))
        = ((Nat.choose n (2 * (k + 1) + 1) : ℤ) * 5 ^ (k + 1))
          + ((Nat.choose n (2 * (k + 1)) : ℤ) * 5 ^ (k + 1)) := by
    intro k _
    rw [pascal_odd n k]
    push_cast
    ring
  have hL1 : (∑ k ∈ Finset.range (n + 1 + 1),
        ((Nat.choose (n + 1) (2 * k + 1) : ℤ) * 5 ^ k))
      = ((n : ℤ) + 1) + (∑ k ∈ Finset.range n,
        ((Nat.choose (n + 1) (2 * (k + 1) + 1) : ℤ) * 5 ^ (k + 1))) := by
    rw [Finset.sum_range_succ', hF0, Finset.sum_range_succ, hFn1, add_zero]
    exact add_comm _ _
  have hH1 : (∑ k ∈ Finset.range (n + 1), ((Nat.choose n (2 * k + 1) : ℤ) * 5 ^ k))
      = (n : ℤ) + (∑ k ∈ Finset.range n,
        ((Nat.choose n (2 * (k + 1) + 1) : ℤ) * 5 ^ (k + 1))) := by
    rw [Finset.sum_range_succ', hH0]
    exact add_comm _ _
  have hE1 : (∑ k ∈ Finset.range (n + 1), ((Nat.choose n (2 * k) : ℤ) * 5 ^ k))
      = 1 + (∑ k ∈ Finset.range n,
        ((Nat.choose n (2 * (k + 1)) : ℤ) * 5 ^ (k + 1))) := by
    rw [Finset.sum_range_succ', hG0]
    exact add_comm _ _
  have hsum : (∑ k ∈ Finset.range n,
        ((Nat.choose (n + 1) (2 * (k + 1) + 1) : ℤ) * 5 ^ (k + 1)))
      = (∑ k ∈ Finset.range n, ((Nat.choose n (2 * (k + 1) + 1) : ℤ) * 5 ^ (k + 1)))
        + (∑ k ∈ Finset.range n, ((Nat.choose n (2 * (k + 1)) : ℤ) * 5 ^ (k + 1))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl key
  unfold evenSum oddSum
  rw [hL1, hH1, hE1]
  linear_combination hsum

/-- Second-order recurrence for the odd part. -/
private lemma oddSum_two_step (n : ℕ) :
    oddSum (n + 2) = 2 * oddSum (n + 1) + 4 * oddSum n := by
  have h1 := evenSum_step n
  have h2 := oddSum_step n
  have h3 := oddSum_step (n + 1)
  linear_combination h3 + h1 - h2

/-- Closed form: twice the odd part is `2^n * F_n`. -/
private lemma oddSum_mul_two (n : ℕ) :
    2 * oddSum n = (2 ^ n : ℤ) * (Nat.fib n : ℤ) := by
  have h13 : Nat.choose 1 3 = 0 := rfl
  have ho0 : oddSum 0 = 0 := by
    unfold oddSum
    simp
  have ho1 : oddSum 1 = 1 := by
    unfold oddSum
    show (∑ k ∈ Finset.range 2, ((Nat.choose 1 (2 * k + 1) : ℤ) * 5 ^ k)) = 1
    rw [Finset.sum_range_succ, Finset.sum_range_one]
    simp [h13]
  have pair : ∀ n : ℕ, 2 * oddSum n = (2 ^ n : ℤ) * (Nat.fib n : ℤ)
      ∧ 2 * oddSum (n + 1) = (2 ^ (n + 1) : ℤ) * (Nat.fib (n + 1) : ℤ) := by
    intro n
    induction n with
    | zero =>
      rw [ho0, ho1]
      simp [Nat.fib_zero, Nat.fib_one]
    | succ n ih =>
      obtain ⟨h1, h2⟩ := ih
      refine ⟨h2, ?_⟩
      have hO := oddSum_two_step n
      have hF : ((Nat.fib (n + 2) : ℤ)) = Nat.fib n + Nat.fib (n + 1) := by
        exact_mod_cast Nat.fib_add_two
      have e1 : n + 1 + 1 = n + 2 := rfl
      rw [e1]
      linear_combination 2 * hO + 2 * h2 + 4 * h1 - (2 ^ (n + 2)) * hF
  exact (pair n).1

/-- `C(p-1,j) ≡ (-1)^j` in `ZMod p` for `j ≤ p - 1`. -/
private lemma choose_sub_one (p : ℕ) [Fact (Nat.Prime p)] (j : ℕ) (hj : j ≤ p - 1) :
    ((Nat.choose (p - 1) j : ℕ) : ZMod p) = (-1) ^ j := by
  have hp1 : 1 ≤ p := Nat.Prime.pos (Fact.out)
  have key : ∀ j : ℕ, j ≤ p - 1 →
      ((Nat.choose (p - 1) j : ℕ) : ZMod p) = (-1) ^ j := by
    intro j
    induction j with
    | zero =>
      intro
      simp
    | succ j ih =>
      intro hj
      have hjp : j + 1 < p := by omega
      have hpos : j + 1 ≠ 0 := by omega
      have hdvd := (Fact.out : Nat.Prime p).dvd_choose_self hpos hjp
      have h0 : ((Nat.choose p (j + 1) : ℕ) : ZMod p) = 0 := by
        rw [CharP.cast_eq_zero_iff (ZMod p) p]
        exact hdvd
      have hpas : Nat.choose p (j + 1)
          = Nat.choose (p - 1) j + Nat.choose (p - 1) (j + 1) := by
        have h := Nat.choose_succ_succ (p - 1) j
        have e1 : (p - 1).succ = p := by omega
        have e2 : j.succ = j + 1 := by omega
        rwa [e1, e2] at h
      have hpas' : ((Nat.choose p (j + 1) : ℕ) : ZMod p)
          = ((Nat.choose (p - 1) j : ℕ) : ZMod p)
            + ((Nat.choose (p - 1) (j + 1) : ℕ) : ZMod p) := by
        rw [hpas, Nat.cast_add]
      have e1 := ih (by omega : j ≤ p - 1)
      rw [h0, e1] at hpas'
      have e2 : (-1 : ZMod p) ^ (j + 1) = -(-1) ^ j := by
        rw [pow_succ]
        ring
      rw [e2]
      linear_combination -hpas'
  exact key j hj

/-- Cast of the closed form to `ZMod p`. -/
private lemma oddSum_mul_two_mod (n p : ℕ) :
    (2 : ZMod p) * ((oddSum n : ℤ) : ZMod p)
      = (2 : ZMod p) ^ n * ((Nat.fib n : ℕ) : ZMod p) := by
  have hcast : ((2 * oddSum n : ℤ) : ZMod p)
      = ((((2 ^ n : ℤ) * (Nat.fib n : ℤ)) : ℤ) : ZMod p) :=
    congrArg (Int.cast : ℤ → ZMod p) (oddSum_mul_two n)
  rw [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_ofNat,
    Int.cast_natCast] at hcast
  exact hcast

/--
**Fibonacci prime divisibility.** Let $p$ be a prime with $p > 2$ and $p \ne 5$, and let
$\left(\frac{5}{p}\right)$ be the Legendre symbol of $5$ modulo $p$. Then $p$ divides the
Fibonacci number $F_{p-1}$ if $\left(\frac{5}{p}\right) = 1$, and $p$ divides the Fibonacci
number $F_{p+1}$ otherwise. Since $\left(\frac{5}{p}\right) = \pm 1$, this says that $p$ divides
$F_{p - \left(\frac{5}{p}\right)}$.

Proves `Wanted` entry `fib_prime_dvd_fib_of_legendre_sub`.

Source: Phakhinkon Phunphayap and Prapanpong Pongsriiam,
"Explicit Formulas for the p-adic Valuations of Fibonomial Coefficients,"
Journal of Integer Sequences 21 (2018), Article 18.3.1,
Lemma (label lemma2.2), item (i), lines 166–169,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Pongsriiam/pong12.tex
-/
theorem fib_prime_dvd_fib_of_legendre_sub
    (p : ℕ) [Fact (Nat.Prime p)] (h5 : p ≠ 5) (h2 : 2 < p) :
    p ∣ Nat.fib (if legendreSym p 5 = 1 then p - 1 else p + 1) := by
  have hp : Nat.Prime p := Fact.out
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨m, hm⟩ := hodd
  have h2ne : ((2 : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hdvd
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
    omega
  have h4ne : ((4 : ℕ) : ZMod p) ≠ 0 := by
    rw [ne_eq, CharP.cast_eq_zero_iff (ZMod p) p]
    intro hdvd
    have h2dvd : p ∣ 2 := by
      have h4eq : (4 : ℕ) = 2 * 2 := rfl
      rw [h4eq] at hdvd
      rcases hp.dvd_mul.mp hdvd with h | h <;> exact h
    have hpeq : p = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2dvd
    omega
  have h5ne : ((5 : ℤ) : ZMod p) ≠ 0 := by
    intro hcon
    have h5nat : ((5 : ℕ) : ZMod p) = 0 := by exact_mod_cast hcon
    rw [CharP.cast_eq_zero_iff (ZMod p) p] at h5nat
    have hpeq : p = 5 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).mp h5nat
    exact h5 hpeq
  have heuler := legendreSym.eq_pow p 5
  have hpm : p / 2 = m := by omega
  rw [hpm] at heuler
  have h2Ne : (2 : ZMod p) ≠ 0 := by exact_mod_cast h2ne
  have hferm2 : (2 : ZMod p) ^ (p - 1) = 1 :=
    ZMod.pow_card_sub_one_eq_one h2Ne
  have e5 : ((5 : ℤ) : ZMod p) = (5 : ZMod p) := by simp
  by_cases hcase : legendreSym p 5 = 1
  · rw [ite_eq_left hcase]
    apply (CharP.cast_eq_zero_iff (ZMod p) p _).mp
    have hidp := oddSum_mul_two_mod (p - 1) p
    rw [hferm2, one_mul] at hidp
    have hO : ((oddSum (p - 1) : ℤ) : ZMod p) = 0 := by
      have hexpand : ((oddSum (p - 1) : ℤ) : ZMod p)
          = ∑ k ∈ Finset.range p, ((Nat.choose (p - 1) (2 * k + 1) : ℕ) : ZMod p)
            * (5 : ZMod p) ^ k := by
        have h1 : p - 1 + 1 = p := by omega
        unfold oddSum
        rw [h1]
        simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
          Int.cast_ofNat]
      rw [hexpand]
      have hterm : ∀ k ∈ Finset.range p,
          ((Nat.choose (p - 1) (2 * k + 1) : ℕ) : ZMod p) * (5 : ZMod p) ^ k
            = if k < m then -((5 : ZMod p) ^ k) else 0 := by
        intro k hk
        by_cases hkm : k < m
        · rw [ite_eq_left hkm]
          have hle : 2 * k + 1 ≤ p - 1 := by omega
          rw [choose_sub_one p (2 * k + 1) hle,
            Odd.neg_one_pow (show Odd (2 * k + 1) from ⟨k, rfl⟩)]
          ring
        · rw [ite_eq_right hkm]
          have hgt : p - 1 < 2 * k + 1 := by omega
          have hC : Nat.choose (p - 1) (2 * k + 1) = 0 :=
            Nat.choose_eq_zero_of_lt hgt
          rw [hC, Nat.cast_zero, zero_mul]
      rw [Finset.sum_congr rfl hterm]
      have hsub : Finset.range m ⊆ Finset.range p := by
        intro x hx
        simp only [Finset.mem_range] at hx ⊢
        omega
      have hzero : ∀ k ∈ Finset.range p, k ∉ Finset.range m →
          (if k < m then -((5 : ZMod p) ^ k) else (0 : ZMod p)) = 0 := by
        intro k _ hkm
        rw [Finset.mem_range] at hkm
        rw [ite_eq_right hkm]
      rw [← Finset.sum_subset hsub hzero]
      have hif : ∀ k ∈ Finset.range m,
          (if k < m then -((5 : ZMod p) ^ k) else (0 : ZMod p))
            = -((5 : ZMod p) ^ k) := by
        intro k hk
        rw [ite_eq_left (Finset.mem_range.mp hk)]
      rw [Finset.sum_congr rfl hif, Finset.sum_neg_distrib, neg_eq_zero]
      have hgeom := geom_sum_mul (5 : ZMod p) m
      have heuler1 : (5 : ZMod p) ^ m = 1 := by
        have h2 := heuler
        rw [hcase] at h2
        rw [e5] at h2
        simpa using h2.symm
      rw [heuler1, sub_self] at hgeom
      have h51 : (5 : ZMod p) - 1 ≠ 0 := by
        have hconv : (5 : ZMod p) - 1 = ((4 : ℕ) : ZMod p) := by
          rw [Nat.cast_ofNat]
          ring
        rwa [hconv]
      exact (mul_eq_zero.mp hgeom).resolve_right h51
    rw [hO, mul_zero] at hidp
    exact hidp.symm
  · have hneg : legendreSym p 5 = -1 := by
      rcases legendreSym.eq_one_or_neg_one (p := p) (a := 5) h5ne with h1 | h1
      · exact absurd h1 hcase
      · exact h1
    rw [ite_eq_right hcase]
    apply (CharP.cast_eq_zero_iff (ZMod p) p _).mp
    have hidp := oddSum_mul_two_mod (p + 1) p
    have hsq : (2 : ZMod p) ^ 2 = 4 := by ring
    have h2p1 : (2 : ZMod p) ^ (p + 1) = 4 := by
      have h : p + 1 = (p - 1) + 2 := by omega
      rw [h, pow_add, hferm2, one_mul, hsq]
    rw [h2p1] at hidp
    have hO : ((oddSum (p + 1) : ℤ) : ZMod p) = 0 := by
      have hexpand : ((oddSum (p + 1) : ℤ) : ZMod p)
          = ∑ k ∈ Finset.range (p + 2),
            ((Nat.choose (p + 1) (2 * k + 1) : ℕ) : ZMod p)
            * (5 : ZMod p) ^ k := by
        have h1 : p + 1 + 1 = p + 2 := by omega
        unfold oddSum
        rw [h1]
        simp only [Int.cast_sum, Int.cast_mul, Int.cast_pow, Int.cast_natCast,
          Int.cast_ofNat]
      rw [hexpand]
      have e2 : ((p + 1 : ℕ) : ZMod p) = 1 := by
        rw [Nat.cast_add, Nat.cast_one, ZMod.natCast_self p, zero_add]
      have ht0 : ((Nat.choose (p + 1) (2 * 0 + 1) : ℕ) : ZMod p)
          * (5 : ZMod p) ^ (0 : ℕ) = 1 := by
        have e1 : (2 * 0 + 1 : ℕ) = 1 := by omega
        rw [e1, Nat.choose_one_right, e2, pow_zero, mul_one]
      have htm : ((Nat.choose (p + 1) (2 * m + 1) : ℕ) : ZMod p)
          * (5 : ZMod p) ^ m = -1 := by
        have e1 : 2 * m + 1 = p := hm.symm
        rw [e1, Nat.choose_succ_self_right, e2, one_mul]
        have h2 := heuler
        rw [hneg] at h2
        rw [e5] at h2
        simpa using h2.symm
      have hrest : ∀ k ∈ Finset.range (p + 2), k ≠ 0 → k ≠ m →
          ((Nat.choose (p + 1) (2 * k + 1) : ℕ) : ZMod p)
            * (5 : ZMod p) ^ k = 0 := by
        intro k hk hk0 hkm
        by_cases hj : 2 * k + 1 ≤ p + 1
        · have hjm : 2 * k + 1 ≠ p := by omega
          have hjp1 : 2 * k + 1 ≠ p + 1 := by omega
          have hjlt : 2 * k + 1 < p := by omega
          have hpas : Nat.choose (p + 1) (2 * k + 1)
              = Nat.choose p (2 * k + 1 - 1) + Nat.choose p (2 * k + 1) := by
            have hps := Nat.choose_succ_succ p (2 * k + 1 - 1)
            have e1 : p.succ = p + 1 := by omega
            have e2 : (2 * k + 1 - 1).succ = 2 * k + 1 := by omega
            rwa [e1, e2] at hps
          have d1 : p ∣ Nat.choose p (2 * k + 1) :=
            hp.dvd_choose_self (by omega) hjlt
          have d2 : p ∣ Nat.choose p (2 * k + 1 - 1) :=
            hp.dvd_choose_self (by omega) (by omega)
          have hdvd : p ∣ Nat.choose (p + 1) (2 * k + 1) := by
            rw [hpas]
            exact Nat.dvd_add d2 d1
          have h0 : ((Nat.choose (p + 1) (2 * k + 1) : ℕ) : ZMod p) = 0 := by
            rw [CharP.cast_eq_zero_iff (ZMod p) p]
            exact hdvd
          rw [h0, zero_mul]
        · have hgt : p + 1 < 2 * k + 1 := by omega
          have hC : Nat.choose (p + 1) (2 * k + 1) = 0 :=
            Nat.choose_eq_zero_of_lt hgt
          rw [hC, Nat.cast_zero, zero_mul]
      have h0mem : 0 ∈ Finset.range (p + 2) := by
        simp only [Finset.mem_range]
        omega
      have hmmem : m ∈ (Finset.range (p + 2)).erase 0 := by
        simp only [Finset.mem_erase, Finset.mem_range]
        omega
      rw [← Finset.add_sum_erase _ _ h0mem, ht0,
        ← Finset.add_sum_erase _ _ hmmem, htm]
      have hzero : (∑ x ∈ (Finset.range (p + 2)).erase 0 |>.erase m,
          ((Nat.choose (p + 1) (2 * x + 1) : ℕ) : ZMod p)
            * (5 : ZMod p) ^ x) = 0 := by
        apply Finset.sum_eq_zero
        intro k hk
        simp only [Finset.mem_erase, Finset.mem_range] at hk
        obtain ⟨hkm, hk0, hkr⟩ := hk
        exact hrest k (Finset.mem_range.mpr hkr) hk0 hkm
      rw [hzero]
      ring
    rw [hO, mul_zero] at hidp
    have h4Ne : (4 : ZMod p) ≠ 0 := by exact_mod_cast h4ne
    exact (mul_eq_zero.mp hidp.symm).resolve_left h4Ne

end MetaMathlibExt
