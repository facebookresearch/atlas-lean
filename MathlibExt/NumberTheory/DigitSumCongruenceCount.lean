/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Int.ModEq
public import Mathlib.Data.Rat.Defs
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.Ring
import MathlibExt.Data.Int.CardIntervalMod

/-!
# Digit-sum congruence counts

When the base is `1` modulo the modulus, the distribution of tail digit sums is uniform apart
from a single extra count in the zero residue class. We prove this by adjoining one digit at a
time, then sum over the leading interval. The leading coordinate need not be less than the base.

## References

* Kritkhajohn Onphaeng, Tammatada Khemaratchatakumthorn, Phakhinkon Napp Phunphayap and
  Prapanpong Pongsriiam, *Exact Formulas for the Number of Palindromes in Certain Arithmetic
  Progressions*, Journal of Integer Sequences 27 (2024), Article 24.4.8, pp. 1–29,
  Definition 3 and Lemmas 4 and 5.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Digit-sum congruence count.** For natural numbers $b$, $k$, $q$, $x$, $y$ and an integer $r$,
$N_b(k, q, r, x, y)$ is the number of tuples $(x_1, \dots, x_k)$ of natural numbers with
$x \le x_1 < y$ and $x_i < b$ for $2 \le i \le k$ such that $x_1 + \dots + x_k \equiv r \pmod q$.
The count is meant for $k \ge 1$; for $k = 0$ it is defined to equal its value for $k = 1$, the
number of natural numbers $x_1$ with $x \le x_1 < y$ and $x_1 \equiv r \pmod q$.

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Definition 3. -/
public def digitSumCongruenceCount (b k q : ℕ) (r : ℤ) (x y : ℕ) : ℕ :=
  ((Finset.Ico x y ×ˢ Fintype.piFinset fun _ : Fin (k - 1) => Finset.range b).filter
    fun p => ((p.1 + ∑ i, p.2 i : ℕ) : ℤ) ≡ r [ZMOD q]).card

end

open Finset

private def digitTails (b n : ℕ) : Finset (Fin n → ℕ) :=
  Fintype.piFinset fun _ => range b

private def residueIndicator (q : ℕ) (r s : ℤ) : ℚ :=
  if s ≡ r [ZMOD q] then 1 else 0

private theorem residueIndicator_add (q : ℕ) (r s t : ℤ) :
    residueIndicator q r (s + t) = residueIndicator q (r - s) t := by
  have h : s + t ≡ r [ZMOD q] ↔ t ≡ r - s [ZMOD q] := by
    have hr : s + (r - s) = r := by omega
    constructor
    · intro h
      apply Int.ModEq.add_left_cancel' s
      rwa [hr]
    · intro h
      simpa only [hr] using h.add_left s
  simp only [residueIndicator, h]

private theorem residueIndicator_sub_zero (q : ℕ) (r s : ℤ) :
    residueIndicator q (r - s) 0 = residueIndicator q r s := by
  simpa only [add_zero] using (residueIndicator_add q r s 0).symm

private theorem residueIndicator_zero (q : ℕ) (r : ℤ) :
    residueIndicator q r 0 = (if r ≡ 0 [ZMOD q] then 1 else 0) := by
  simp only [residueIndicator, Int.modEq_comm (a := 0)]

private theorem sum_residueIndicator_range (a : ℕ) {q : ℕ} (hq : 0 < q) (r : ℤ) :
    ∑ i ∈ range a, residueIndicator q r i =
      (↑(a / q) : ℚ) + (if r % q < ((a % q : ℕ) : ℤ) then 1 else 0) := by
  calc
    _ = ∑ i ∈ (range a).filter (fun i : ℕ => (i : ℤ) ≡ r [ZMOD q]), (1 : ℚ) := by
      rw [sum_filter]
      rfl
    _ = (Nat.count (fun i : ℕ => (i : ℤ) ≡ r [ZMOD q]) a : ℚ) := by
      simp [Nat.count_eq_card_filter_range, sum_const, nsmul_eq_mul]
    _ = _ := by rw [Nat.count_intModEq_card hq, Nat.cast_add]; simp only [Nat.cast_ite,
      Nat.cast_one, Nat.cast_zero]

-- The last point of [0,b) is a multiple of q, and the preceding points form complete blocks.
private theorem sum_residueIndicator_base {b q : ℕ} (hb : 1 ≤ b) (hq : 0 < q)
    (hbq : b ≡ 1 [MOD q]) (r : ℤ) :
    ∑ i ∈ range b, residueIndicator q r i = ((b : ℚ) - 1) / q + residueIndicator q r 0 := by
  have hd := (Nat.modEq_iff_dvd' hb).mp hbq.symm
  have hlast : ((b - 1 : ℕ) : ℤ) ≡ 0 [ZMOD q] := by
    exact Int.modEq_zero_iff_dvd.mpr (by exact_mod_cast hd)
  have hind : residueIndicator q r (b - 1 : ℕ) = residueIndicator q r 0 := by
    have h : ((b - 1 : ℕ) : ℤ) ≡ r [ZMOD q] ↔ 0 ≡ r [ZMOD q] :=
      ⟨fun h => hlast.symm.trans h, fun h => hlast.trans h⟩
    simp only [residueIndicator, h]
  have hdiv : (↑((b - 1) / q) : ℚ) = ((b : ℚ) - 1) / q := by
    apply (eq_div_iff (by exact_mod_cast hq.ne' : (q : ℚ) ≠ 0)).2
    rw [← Nat.cast_one (R := ℚ), ← Nat.cast_sub hb, ← Nat.cast_mul, Nat.div_mul_cancel hd]
  conv_lhs => rw [← Nat.sub_add_cancel hb, sum_range_succ]
  rw [hind, sum_residueIndicator_range _ hq, Nat.mod_eq_zero_of_dvd hd, hdiv]
  simp [Int.emod_nonneg _ (by exact_mod_cast hq.ne' : (q : ℤ) ≠ 0)]

private theorem sum_digitTails_succ {b n : ℕ} (f : (Fin (n + 1) → ℕ) → ℚ) :
    ∑ t ∈ digitTails b (n + 1), f t =
      ∑ x ∈ range b, ∑ t ∈ digitTails b n, f (Fin.cons x t) := by
  rw [← sum_product (range b) (digitTails b n) (fun p => f (Fin.cons p.1 p.2))]
  symm
  apply sum_equiv (Fin.consEquiv fun _ : Fin (n + 1) => ℕ)
  · intro p
    simp [digitTails, Fin.consEquiv_apply, Fin.forall_fin_succ]
  · intro p _
    rfl

private def tailCount (b n q : ℕ) (r : ℤ) : ℚ :=
  ∑ t ∈ digitTails b n, residueIndicator q r (∑ i, t i : ℕ)

-- Adjoining a digit preserves the uniform part and convolves the exceptional zero term
-- with the single-digit distribution.
private theorem tailCount_eq {b q : ℕ} (hb : 1 ≤ b) (hq : 0 < q) (hbq : b ≡ 1 [MOD q])
    (n : ℕ) (r : ℤ) : tailCount b n q r = ((b : ℚ) ^ n - 1) / q + residueIndicator q r 0 := by
  induction n generalizing r with
  | zero => simp [tailCount, digitTails]
  | succ n ih =>
    have hstep (x : ℕ) (t : Fin n → ℕ) :
        residueIndicator q r (∑ i, Fin.cons (α := fun _ => ℕ) x t i : ℕ) =
          residueIndicator q (r - x) (∑ i, t i : ℕ) := by
      rw [Fin.sum_univ_succ]
      simpa only [Fin.cons_zero, Fin.cons_succ, Nat.cast_add] using
        residueIndicator_add q r x (∑ i, t i : ℕ)
    calc
      _ = ∑ x ∈ range b, tailCount b n q (r - x) := by
        rw [tailCount, sum_digitTails_succ]
        simp only [tailCount, hstep]
      _ = ∑ x ∈ range b, (((b : ℚ) ^ n - 1) / q + residueIndicator q r x) := by
        apply sum_congr rfl
        intro x _
        simp only [ih, residueIndicator_sub_zero]
      _ = _ := by
        rw [sum_add_distrib, sum_const, card_range, sum_residueIndicator_base hb hq hbq,
          nsmul_eq_mul, pow_succ]
        ring

private theorem digitSumCongruenceCount_eq {b q : ℕ} (hb : 1 ≤ b) (hq : 0 < q)
    (hbq : b ≡ 1 [MOD q]) (k : ℕ) (r : ℤ) (x y : ℕ) :
    (digitSumCongruenceCount b k q r x y : ℚ) =
      (↑(#(Ico x y)) : ℚ) * (((b : ℚ) ^ (k - 1) - 1) / q) +
        ∑ i ∈ Ico x y, residueIndicator q r i := by
  have hstep (i : ℕ) (t : Fin (k - 1) → ℕ) :
      residueIndicator q r ((i + ∑ j, t j : ℕ) : ℤ) =
        residueIndicator q (r - i) (∑ j, t j : ℕ) := by
    rw [Nat.cast_add, residueIndicator_add]
  calc
    _ = ∑ p ∈ (Ico x y ×ˢ digitTails b (k - 1)),
        residueIndicator q r ((p.1 + ∑ i, p.2 i : ℕ) : ℤ) := by
      rw [digitSumCongruenceCount, ← nsmul_one (A := ℚ), ← sum_const, sum_filter]
      rfl
    _ = ∑ i ∈ Ico x y, tailCount b (k - 1) q (r - i) := by
      rw [sum_product]
      simp only [hstep, tailCount]
    _ = _ := by
      simp_rw [tailCount_eq hb hq hbq, residueIndicator_sub_zero]
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul]

/-- **Counting digit tuples by their sum modulo a divisor of the base minus one.** Let $a$, $b$,
$k$ and $q$ be natural numbers, all at least $1$, with $b \equiv 1 \pmod q$, and let $r$ be an
integer. For natural numbers $x$ and $y$ write $N_b(k, q, r, x, y)$ for the number of tuples
$(x_1, \dots, x_k)$ of natural numbers with $x \le x_1 < y$, $x_i < b$ for $2 \le i \le k$, and
$x_1 + \dots + x_k \equiv r \pmod q$. Write $[P]$ for $1$ if $P$ holds and $0$ otherwise,
$\lfloor a/q \rfloor$ for the integer part of $a/q$, and $r \bmod q$ and $a \bmod q$ for the least
nonnegative residues modulo $q$. Then, as rational numbers,

$$N_b(k, q, r, 0, b) = \frac{b^k - 1}{q} + [r \equiv 0 \pmod q],$$

$$N_b(k, q, r, 1, b) = \frac{b^k - b^{k-1}}{q},$$

$$N_b(k, q, r, 0, a) = \frac{a (b^{k-1} - 1)}{q} + \lfloor a/q \rfloor + [r \bmod q < a \bmod q],$$

$$N_b(k, q, r, 1, a) = \frac{(a - 1)(b^{k-1} - 1)}{q} + \lfloor a/q \rfloor +
[r \bmod q < a \bmod q] - [r \equiv 0 \pmod q].$$

Source: K. Onphaeng, T. Khemaratchatakumthorn, P. N. Phunphayap and P. Pongsriiam, *Exact
Formulas for the Number of Palindromes in Certain Arithmetic Progressions*, Journal of Integer
Sequences 27 (2024), Article 24.4.8, Lemma 5. -/
public theorem digitSumCongruenceCount_of_modEq_one {a b k q : ℕ} (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hk : 1 ≤ k) (hq : 1 ≤ q) (hbq : b ≡ 1 [MOD q]) (r : ℤ) :
    (digitSumCongruenceCount b k q r 0 b : ℚ) =
        ((b : ℚ) ^ k - 1) / q + (if r ≡ 0 [ZMOD q] then 1 else 0) ∧
      (digitSumCongruenceCount b k q r 1 b : ℚ) = ((b : ℚ) ^ k - (b : ℚ) ^ (k - 1)) / q ∧
      (digitSumCongruenceCount b k q r 0 a : ℚ) =
        (a : ℚ) * ((b : ℚ) ^ (k - 1) - 1) / q + ((a / q : ℕ) : ℚ) +
          (if r % q < ((a % q : ℕ) : ℤ) then 1 else 0) ∧
      (digitSumCongruenceCount b k q r 1 a : ℚ) =
        ((a : ℚ) - 1) * ((b : ℚ) ^ (k - 1) - 1) / q + ((a / q : ℕ) : ℚ) +
          (if r % q < ((a % q : ℕ) : ℤ) then 1 else 0) - (if r ≡ 0 [ZMOD q] then 1 else 0) := by
  have hq' : 0 < q := by omega
  have hzero (c : ℕ) :
      (digitSumCongruenceCount b k q r 0 c : ℚ) =
        (c : ℚ) * (((b : ℚ) ^ (k - 1) - 1) / q) + ∑ i ∈ range c, residueIndicator q r i := by
    simpa only [Nat.Ico_zero_eq_range, card_range] using
      digitSumCongruenceCount_eq hb hq' hbq k r 0 c
  have hone (c : ℕ) (hc : 1 ≤ c) :
      (digitSumCongruenceCount b k q r 1 c : ℚ) =
        ((c : ℚ) - 1) * (((b : ℚ) ^ (k - 1) - 1) / q) +
          (∑ i ∈ range c, residueIndicator q r i) - residueIndicator q r 0 := by
    have hsplit : insert 0 (Ico 1 c) = range c := by
      ext i
      simp only [mem_insert, mem_Ico, mem_range]
      omega
    have hsum : (∑ i ∈ range c, residueIndicator q r i) =
        residueIndicator q r 0 + ∑ i ∈ Ico 1 c, residueIndicator q r i := by
      rw [← hsplit, sum_insert (by simp), Nat.cast_zero]
    rw [digitSumCongruenceCount_eq hb hq' hbq, Nat.card_Ico, Nat.cast_sub hc, Nat.cast_one, hsum]
    ring
  have hpow : (b : ℚ) ^ k = (b : ℚ) ^ (k - 1) * b := by
    rw [← pow_succ, Nat.sub_add_cancel hk]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hzero, sum_residueIndicator_base hb hq' hbq, residueIndicator_zero, hpow]
    ring
  · rw [hone b hb, sum_residueIndicator_base hb hq' hbq, hpow]
    ring
  · rw [hzero, sum_residueIndicator_range _ hq']
    ring
  · rw [hone a ha, sum_residueIndicator_range _ hq', residueIndicator_zero]
    ring

end MetaMathlibExt
