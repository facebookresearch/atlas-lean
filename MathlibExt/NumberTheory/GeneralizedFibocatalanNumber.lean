/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Algebra.Order.Star.Rat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum

@[expose] public section

/-!
Source: Killpatrick, JIS VOL 28, `killp6.tex`,
SHA256 `660c140f0fb7d3932abbea93631978efa4b1bf33bb089ba35a36a0556d5c40ec`.
Rank 340, lexical id `jis_term_14f7f012e4513e61c304514a`,
semantic id `jis_sem_959023b7307932f10fb8ebe4`.

Fibonacci-valued FiboCatalan generalization: Fibonacci factorial `F_n! `,
Jordan-type quotient `J_{r,F} = F_{2r+1}! / F_r! `, and the generalized
FiboCatalan number `J_{r,F} * F_{2n}! / (F_n! * F_{n+r+1}!)`.

This file treats the Fibonacci-valued case and supplies a divisibility criterion for
products of Fibonacci factorials, also used for the super FiboCatalan numbers.
-/

namespace MetaMathlibExt

section
/-- **Fibonacci factorial.** For a natural number $n$, the Fibonacci factorial $F_n!$ is the
rational number $F_n! = F_1 F_2 \cdots F_n$, the product of the first $n$ Fibonacci numbers
(where $F_1 = F_2 = 1$ and $F_{k+2} = F_{k+1} + F_k$); in particular $F_0! = 1$, the empty
product.

Values are taken in $\mathbb{Q}$ so that quotients of Fibonacci factorials are exact rather
than truncated by natural-number division. -/
def fibonacciFactorial : ℕ → ℚ
  | 0 => 1
  | n + 1 => fibonacciFactorial n * (Nat.fib (n + 1) : ℚ)

/-- **Fibonacci factorial at zero.** The Fibonacci factorial $F_0!$ equals $1$, by the
empty-product convention. -/
theorem fibonacciFactorial_zero :
    fibonacciFactorial 0 = 1 := rfl

/-- **Fibonacci factorials are positive.** For every natural number $n$, the Fibonacci factorial
$F_n!$ is a strictly positive rational number. -/
theorem fibonacciFactorial_pos (n : ℕ) :
    0 < fibonacciFactorial n := by
  induction n with
  | zero =>
    simp only [fibonacciFactorial, zero_lt_one]
  | succ n ih =>
    simp only [fibonacciFactorial]
    apply mul_pos ih
    exact Nat.cast_pos.mpr (Nat.fib_pos.mpr (Nat.succ_pos n))

/-- **Fibonacci factorials are nonzero.** For every natural number $n$, the Fibonacci factorial
$F_n!$ is a nonzero rational number. -/
theorem fibonacciFactorial_ne (n : ℕ) :
    fibonacciFactorial n ≠ 0 :=
  ne_of_gt (fibonacciFactorial_pos n)

/-- **Fibonacci factorial at one.** The Fibonacci factorial $F_1!$ equals $1$, since the first
Fibonacci number is $F_1 = 1$. -/
theorem fibonacciFactorial_one :
    fibonacciFactorial 1 = 1 := by
  have hfib1 : Nat.fib 1 = 1 := by decide
  have h : fibonacciFactorial 1
      = fibonacciFactorial 0 * (Nat.fib 1 : ℚ) := rfl
  rw [h, hfib1, Nat.cast_one, fibonacciFactorial_zero, one_mul]

/-- **Fibonacci factorial at two.** The Fibonacci factorial $F_2! = F_1 F_2$ of the Fibonacci
numbers $F_1, F_2$ equals $1$, since $F_1 = F_2 = 1$. -/
theorem fibonacciFactorial_two :
    fibonacciFactorial 2 = 1 := by
  have hfib2 : Nat.fib 2 = 1 := by decide
  have h : fibonacciFactorial 2
      = fibonacciFactorial 1 * (Nat.fib 2 : ℚ) := rfl
  rw [h, hfib2, Nat.cast_one, fibonacciFactorial_one, one_mul]

/-- **Fibonacci factorial at three.** The Fibonacci factorial $F_3! = F_1 F_2 F_3$ of the
Fibonacci numbers $F_1, F_2, F_3$ equals $2$, since $F_1 = F_2 = 1$ and $F_3 = 2$. -/
theorem fibonacciFactorial_three :
    fibonacciFactorial 3 = 2 := by
  have hfib3 : Nat.fib 3 = 2 := by decide
  have h : fibonacciFactorial 3
      = fibonacciFactorial 2 * (Nat.fib 3 : ℚ) := rfl
  rw [h, hfib3, fibonacciFactorial_two]
  norm_num

/-- **Fibonacci Jordan quotient.** For a natural number $r$, the Jordan-type quotient is the
rational number $J_{r,F} = F_{2r+1}! / F_r!$, where $F_m! = F_1 F_2 \cdots F_m$ is the Fibonacci
factorial of the Fibonacci numbers $F_1 = F_2 = 1$, $F_{k+2} = F_{k+1} + F_k$ (so $F_0! = 1$). -/
def fibonacciJordanQuotient (r : ℕ) : ℚ :=
  fibonacciFactorial (2 * r + 1) / fibonacciFactorial r

/-- **Fibonacci Jordan quotient is positive.** For every natural number $r$, the Jordan-type
quotient $J_{r,F} = F_{2r+1}! / F_r!$ of Fibonacci factorials is a strictly positive rational
number. -/
theorem fibonacciJordanQuotient_pos (r : ℕ) :
    0 < fibonacciJordanQuotient r := by
  unfold fibonacciJordanQuotient
  apply div_pos
  · exact fibonacciFactorial_pos _
  · exact fibonacciFactorial_pos _

/-- **Fibonacci Jordan quotient at zero.** The Jordan-type quotient $J_{r,F} = F_{2r+1}! / F_r!$
of Fibonacci factorials takes the value $J_{0,F} = F_1! / F_0! = 1$. -/
theorem fibonacciJordanQuotient_r0 :
    fibonacciJordanQuotient 0 = 1 := by
  have e : 2 * 0 + 1 = 1 := by decide
  unfold fibonacciJordanQuotient
  rw [e, fibonacciFactorial_one, fibonacciFactorial_zero]
  exact div_self (by norm_num)

/-- **Fibonacci Jordan quotient at one.** The Jordan-type quotient $J_{r,F} = F_{2r+1}! / F_r!$
of Fibonacci factorials takes the value $J_{1,F} = F_3! / F_1! = 2$. -/
theorem fibonacciJordanQuotient_r1 :
    fibonacciJordanQuotient 1 = 2 := by
  have e : 2 * 1 + 1 = 3 := by decide
  unfold fibonacciJordanQuotient
  rw [e, fibonacciFactorial_three, fibonacciFactorial_one]
  norm_num

/-- **Generalized FiboCatalan numbers.** Let $F_m! = F_1 F_2 \cdots F_m$ denote the Fibonacci
factorial of the Fibonacci numbers $F_1 = F_2 = 1$, $F_{k+2} = F_{k+1} + F_k$ (so $F_0! = 1$),
and let $J_{r,F} = F_{2r+1}! / F_r!$ be the Fibonacci Jordan quotient. For natural numbers $r$
and $n$, the generalized FiboCatalan number with parameters $r$ and $n$ is the rational number
$J_{r,F} \, F_{2n}! / (F_n! \, F_{n+r+1}!)$. -/
def generalizedFibonacciCatalan (r n : ℕ) : ℚ :=
  fibonacciJordanQuotient r * fibonacciFactorial (2 * n) /
    (fibonacciFactorial n * fibonacciFactorial (n + r + 1))

/-- **Positivity of generalized FiboCatalan numbers.** For all natural numbers $r$ and $n$, the
generalized FiboCatalan number with parameters $r$ and $n$ is a strictly positive rational
number. -/
theorem generalizedFibonacciCatalan_pos (r n : ℕ) :
    0 < generalizedFibonacciCatalan r n := by
  unfold generalizedFibonacciCatalan
  apply div_pos
  · apply mul_pos
    · exact fibonacciJordanQuotient_pos r
    · exact fibonacciFactorial_pos _
  · apply mul_pos
    · exact fibonacciFactorial_pos _
    · exact fibonacciFactorial_pos _

/-- Nat-valued Fibonacci factorial: product of `fib (i+1)` for `i < N`. -/
private def fibFactNat (N : ℕ) : ℕ := ∏ i ∈ Finset.range N, Nat.fib (i + 1)

private theorem fibFactNat_pos (N : ℕ) : 0 < fibFactNat N := by
  unfold fibFactNat
  apply Finset.prod_pos
  intro i _
  exact Nat.fib_pos.mpr (Nat.succ_pos i)

private theorem fibFactNat_ne_zero (N : ℕ) : fibFactNat N ≠ 0 :=
  ne_of_gt (fibFactNat_pos N)

private theorem fibFactNat_mem_dvd (N i : ℕ) (hi : i ∈ Finset.range N) :
    Nat.fib (i + 1) ∣ fibFactNat N :=
  Finset.dvd_prod_of_mem _ hi

/-- Rank of apparition: `p^(t+1) ∣ fib m ↔ d ∣ m`,
when `d` is minimal with the divisibility. -/
private theorem fib_pow_dvd_iff (p t d : ℕ) (hd1 : 1 ≤ d)
    (hdvd : p ^ (t + 1) ∣ Nat.fib d)
    (hmin : ∀ m : ℕ, 1 ≤ m → p ^ (t + 1) ∣ Nat.fib m → d ≤ m)
    (m : ℕ) :
    (p ^ (t + 1) ∣ Nat.fib m ↔ d ∣ m) := by
  constructor
  · intro h
    have hg1 : 1 ≤ Nat.gcd d m :=
      Nat.pos_of_dvd_of_pos (Nat.gcd_dvd_left d m) (by omega)
    have hfib : p ^ (t + 1) ∣ Nat.fib (Nat.gcd d m) := by
      rw [Nat.fib_gcd]
      exact Nat.dvd_gcd hdvd h
    have hle : d ≤ Nat.gcd d m := hmin _ hg1 hfib
    have hge : Nat.gcd d m ≤ d := Nat.gcd_le_left m (by omega)
    have heq : Nat.gcd d m = d := by omega
    rw [← heq]
    exact Nat.gcd_dvd_right d m
  · intro h
    exact hdvd.trans (Nat.fib_dvd _ _ h)

/-- The level count when the level is inhabited: equals `N / d`. -/
private theorem level_count (p t N : ℕ)
    (h : ∃ m : ℕ, 1 ≤ m ∧ p ^ (t + 1) ∣ Nat.fib m) :
    ((Finset.range N).filter (fun i => p ^ (t + 1) ∣ Nat.fib (i + 1))).card
      = N / Nat.find h := by
  have hspec := Nat.find_spec h
  have hd1 : 1 ≤ Nat.find h := hspec.1
  have hdvd : p ^ (t + 1) ∣ Nat.fib (Nat.find h) := hspec.2
  have hmin : ∀ m : ℕ, 1 ≤ m → p ^ (t + 1) ∣ Nat.fib m → Nat.find h ≤ m := by
    intro m hm1 hmd
    exact Nat.find_min' h ⟨hm1, hmd⟩
  have heq : (Finset.range N).filter (fun i => p ^ (t + 1) ∣ Nat.fib (i + 1))
      = (Finset.range N).filter (fun i => Nat.find h ∣ (i + 1)) := by
    apply Finset.filter_congr
    intro i _
    exact fib_pow_dvd_iff p t (Nat.find h) hd1 hdvd hmin (i + 1)
  rw [heq, Nat.card_multiples]

/-- The level count when the level is empty: equals `0`. -/
private theorem level_count_zero (p t N : ℕ)
    (h : ¬ ∃ m : ℕ, 1 ≤ m ∧ p ^ (t + 1) ∣ Nat.fib m) :
    ((Finset.range N).filter (fun i => p ^ (t + 1) ∣ Nat.fib (i + 1))).card
      = 0 := by
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro x _ hx
  exact h ⟨x + 1, by omega, hx⟩

/-- Factorization is monotone under divisibility. -/
private theorem factorization_le_of_dvd (a b p : ℕ) (h : a ∣ b) (hb : b ≠ 0) :
    a.factorization p ≤ b.factorization p := by
  obtain ⟨c, rfl⟩ := h
  have ha : a ≠ 0 := by
    rintro rfl
    exact hb (zero_mul c)
  have hc : c ≠ 0 := by
    rintro rfl
    exact hb (mul_zero a)
  rw [Nat.factorization_mul ha hc]
  exact Nat.le_add_right _ _

/-- Layer cake: factorization of a Fibonacci factorial as a sum of level counts. -/
private theorem fibFactNat_factorization (p N M : ℕ) (hp : p.Prime)
    (hM : ∀ i ∈ Finset.range N, (Nat.fib (i + 1)).factorization p < M) :
    (fibFactNat N).factorization p
      = ∑ t ∈ Finset.range M,
        ((Finset.range N).filter
          (fun i => p ^ (t + 1) ∣ Nat.fib (i + 1))).card := by
  have hne : ∀ x ∈ Finset.range N, Nat.fib (x + 1) ≠ 0 := by
    intro x _
    exact ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos x))
  have hdvdc : ∀ (t i : ℕ),
      (t < (Nat.fib (i + 1)).factorization p ↔ p ^ (t + 1) ∣ Nat.fib (i + 1)) := by
    intro t i
    have hne_i : Nat.fib (i + 1) ≠ 0 :=
      ne_of_gt (Nat.fib_pos.mpr (Nat.succ_pos i))
    rw [Nat.Prime.pow_dvd_iff_le_factorization hp hne_i]
    omega
  have hlayer : ∀ i ∈ Finset.range N,
      (Nat.fib (i + 1)).factorization p
        = ∑ t ∈ Finset.range M,
          (if t < (Nat.fib (i + 1)).factorization p then 1 else 0) := by
    intro i hi
    have hlt := hM i hi
    have hflt : (Finset.range M).filter
          (fun t => t < (Nat.fib (i + 1)).factorization p)
        = Finset.range ((Nat.fib (i + 1)).factorization p) := by
      ext t
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [← Finset.card_filter, hflt, Finset.card_range]
  unfold fibFactNat
  calc (∏ i ∈ Finset.range N, Nat.fib (i + 1)).factorization p
        = ∑ i ∈ Finset.range N, (Nat.fib (i + 1)).factorization p :=
          Nat.factorization_prod_apply hne
      _ = ∑ i ∈ Finset.range N, ∑ t ∈ Finset.range M,
            (if t < (Nat.fib (i + 1)).factorization p then 1 else 0) :=
          Finset.sum_congr rfl (fun i hi => hlayer i hi)
      _ = ∑ t ∈ Finset.range M, ∑ i ∈ Finset.range N,
            (if t < (Nat.fib (i + 1)).factorization p then 1 else 0) :=
          Finset.sum_comm
      _ = ∑ t ∈ Finset.range M, ((Finset.range N).filter
            (fun i => p ^ (t + 1) ∣ Nat.fib (i + 1))).card := by
          apply Finset.sum_congr rfl
          intro t _
          rw [← Finset.card_filter]
          congr 1
          apply Finset.filter_congr
          intro i _
          exact hdvdc t i

/-- Floor inequality at a single prime-power level. -/
private theorem floor_ineq (d r n : ℕ) (hd : 0 < d) :
    r / d + n / d + (n + r + 1) / d ≤ (2 * r + 1) / d + (2 * n) / d := by
  have ham : r % d < d := Nat.mod_lt _ hd
  have hbm : n % d < d := Nat.mod_lt _ hd
  have hr : r = d * (r / d) + r % d := by
    have h := Nat.mod_add_div r d
    omega
  have hn : n = d * (n / d) + n % d := by
    have h := Nat.mod_add_div n d
    omega
  have e1 : n + r + 1 = (n % d + r % d + 1) + d * (n / d + r / d) := by
    linear_combination hr + hn
  have e2 : 2 * r + 1 = (2 * (r % d) + 1) + d * (2 * (r / d)) := by
    linear_combination 2 * hr
  have e3 : 2 * n = (2 * (n % d)) + d * (2 * (n / d)) := by
    linear_combination 2 * hn
  rw [e1, e2, e3, Nat.add_mul_div_left _ _ hd, Nat.add_mul_div_left _ _ hd,
    Nat.add_mul_div_left _ _ hd]
  have hL : (n % d + r % d + 1) / d ≤ 1 := by
    have h2 : (n % d + r % d + 1) / d < 2 := by
      rw [Nat.div_lt_iff_lt_mul hd]
      omega
    omega
  clear hr hn e1 e2 e3 ham hbm
  -- omega misses nonnegativity of `%`-inside-`/` atoms; supply it manually.
  have nn1 : 0 ≤ (n % d + r % d + 1) / d := Nat.zero_le _
  have nn2 : 0 ≤ (2 * (r % d) + 1) / d := Nat.zero_le _
  have nn3 : 0 ≤ (2 * (n % d)) / d := Nat.zero_le _
  by_cases h0 : (n % d + r % d + 1) / d = 0
  · omega
  · have h1 : (n % d + r % d + 1) / d = 1 := by
      rcases (Nat.le_one_iff_eq_zero_or_eq_one.mp hL) with h | h
      · exact absurd h h0
      · exact h
    by_cases hA : (2 * (r % d) + 1) / d = 0
    · by_cases hB : (2 * (n % d)) / d = 0
      · have hge : d ≤ n % d + r % d + 1 := by
          have hle : 1 ≤ (n % d + r % d + 1) / d := by omega
          have h := (Nat.le_div_iff_mul_le hd).mp hle
          omega
        have hltA : 2 * (r % d) + 1 < d := by
          rcases (Nat.div_eq_zero_iff.mp hA) with h | h
          · omega
          · exact h
        have hltB : 2 * (n % d) < d := by
          rcases (Nat.div_eq_zero_iff.mp hB) with h | h
          · omega
          · exact h
        omega
      · omega
    · omega

/-- A floor inequality at every positive index implies divisibility of Fibonacci factorials. -/
private theorem fibFactNat_mul_mul_dvd_mul (a b c u v : ℕ)
    (h : ∀ d : ℕ, 0 < d → a / d + b / d + c / d ≤ u / d + v / d) :
    fibFactNat a * fibFactNat b * fibFactNat c ∣ fibFactNat u * fibFactNat v := by
  have ha := fibFactNat_ne_zero a
  have hb := fibFactNat_ne_zero b
  have hc := fibFactNat_ne_zero c
  have hu := fibFactNat_ne_zero u
  have hv := fibFactNat_ne_zero v
  have hab := mul_ne_zero ha hb
  apply (Nat.factorization_le_iff_dvd (mul_ne_zero hab hc) (mul_ne_zero hu hv)).mp
  intro p
  by_cases hp : p.Prime
  · -- Use a common cutoff for the five prime-power level sums.
    let N := a + b + c + u + v
    let M := (fibFactNat N).factorization p + 1
    let count (x t : ℕ) :=
      ((Finset.range x).filter (fun i => p ^ (t + 1) ∣ Nat.fib (i + 1))).card
    have hf (x : ℕ) (hx : x ≤ N) :
        (fibFactNat x).factorization p = ∑ t ∈ Finset.range M, count x t := by
      apply fibFactNat_factorization p x M hp
      intro i hi
      have hmem : i ∈ Finset.range N :=
        Finset.mem_range.mpr ((Finset.mem_range.mp hi).trans_le hx)
      exact Nat.lt_succ_of_le (factorization_le_of_dvd _ _ p (fibFactNat_mem_dvd N i hmem)
        (fibFactNat_ne_zero N))
    have hsum : (∑ t ∈ Finset.range M, (count a t + count b t + count c t)) ≤
        ∑ t ∈ Finset.range M, (count u t + count v t) := by
      apply Finset.sum_le_sum
      intro t _
      by_cases ht : ∃ i : ℕ, 1 ≤ i ∧ p ^ (t + 1) ∣ Nat.fib i
      · simpa only [count, level_count p t _ ht] using h (Nat.find ht) (Nat.find_spec ht).1
      · simp only [count, level_count_zero p t _ ht, add_zero, le_refl]
    simpa only [Nat.factorization_mul hab hc, Nat.factorization_mul ha hb,
      Nat.factorization_mul hu hv, Finsupp.add_apply, hf a (by dsimp [N]; omega),
      hf b (by dsimp [N]; omega), hf c (by dsimp [N]; omega), hf u (by dsimp [N]; omega),
      hf v (by dsimp [N]; omega), Finset.sum_add_distrib] using hsum
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp]
    exact Nat.zero_le _

/-- The rational Fibonacci factorial is the cast of the natural one. -/
private theorem fibonacciFactorial_eq_cast (N : ℕ) :
    fibonacciFactorial N = (fibFactNat N : ℚ) := by
  induction N with
  | zero =>
    simp [fibonacciFactorial, fibFactNat]
  | succ N ih =>
    simp only [fibonacciFactorial]
    rw [ih]
    have h2 : fibFactNat (N + 1) = fibFactNat N * Nat.fib (N + 1) := by
      unfold fibFactNat
      rw [Finset.prod_range_succ]
    rw [h2, Nat.cast_mul]

-- Shared integrality criterion for the generalized and super FiboCatalan quotients.
lemma fibonacciFactorial_ratio_isPosInt_of_floor_le (a b c u v : ℕ)
    (h : ∀ d : ℕ, 0 < d → a / d + b / d + c / d ≤ u / d + v / d) :
    ∃ k : ℕ, 0 < k ∧ (k : ℚ) = fibonacciFactorial u * fibonacciFactorial v /
      (fibonacciFactorial a * fibonacciFactorial b * fibonacciFactorial c) := by
  obtain ⟨k, hk⟩ := fibFactNat_mul_mul_dvd_mul a b c u v h
  have hden := mul_pos (mul_pos (fibonacciFactorial_pos a) (fibonacciFactorial_pos b))
    (fibonacciFactorial_pos c)
  have hquot : (k : ℚ) = fibonacciFactorial u * fibonacciFactorial v /
      (fibonacciFactorial a * fibonacciFactorial b * fibonacciFactorial c) := by
    apply (eq_div_iff (ne_of_gt hden)).2
    rw [mul_comm (k : ℚ)]
    simp only [fibonacciFactorial_eq_cast]
    exact_mod_cast hk.symm
  refine ⟨k, ?_, hquot⟩
  have hpos := div_pos (mul_pos (fibonacciFactorial_pos u) (fibonacciFactorial_pos v)) hden
  rw [← hquot] at hpos
  exact Nat.cast_pos.mp hpos

/-- **Generalized FiboCatalan numbers are positive integers.** For all natural numbers $r$ and
$n$, the generalized FiboCatalan number with parameters $r$ and $n$ is a positive integer: it
equals $k$ for some natural number $k \ge 1$.

Proves `Wanted` entry `generalizedFibonacciCatalan_isPosInt`.
-/
theorem generalizedFibonacciCatalan_isPosInt (r n : ℕ) :
    ∃ k : ℕ, 0 < k ∧ (k : ℚ) = generalizedFibonacciCatalan r n := by
  obtain ⟨k, hk, h⟩ :=
    fibonacciFactorial_ratio_isPosInt_of_floor_le r n (n + r + 1) (2 * r + 1) (2 * n)
      (fun d hd => floor_ineq d r n hd)
  refine ⟨k, hk, h.trans ?_⟩
  simp only [generalizedFibonacciCatalan, fibonacciJordanQuotient, div_eq_mul_inv, mul_inv_rev]
  ring

/-- **Generalized FiboCatalan numbers at r = 0.** For every natural number $n$, the generalized
FiboCatalan number with parameters $r = 0$ and $n$ equals the FiboCatalan number
$F_{2n}! / (F_n! \, F_{n+1}!)$, where $F_i$ is the $i$-th Fibonacci number ($F_1 = F_2 = 1$) and
$F_m! = F_1 F_2 \cdots F_m$ is the Fibonacci factorial (with $F_0! = 1$). -/
theorem generalizedFibonacciCatalan_r0 (n : ℕ) :
    generalizedFibonacciCatalan 0 n =
      fibonacciFactorial (2 * n) /
        (fibonacciFactorial n * fibonacciFactorial (n + 1)) := by
  unfold generalizedFibonacciCatalan
  rw [fibonacciJordanQuotient_r0, one_mul]

/-- **Generalized FiboCatalan numbers at r = 1.** For every natural number $n$, the generalized
FiboCatalan number with parameters $r = 1$ and $n$ equals $2 F_{2n}! / (F_{n+2}! \, F_n!)$, where
$F_i$ is the $i$-th Fibonacci number ($F_1 = F_2 = 1$) and $F_m! = F_1 F_2 \cdots F_m$ is the
Fibonacci factorial (with $F_0! = 1$). -/
theorem generalizedFibonacciCatalan_r1 (n : ℕ) :
    generalizedFibonacciCatalan 1 n =
      2 * fibonacciFactorial (2 * n) /
        (fibonacciFactorial (n + 2) * fibonacciFactorial n) := by
  unfold generalizedFibonacciCatalan
  rw [fibonacciJordanQuotient_r1]
  have e : n + 1 + 1 = n + 2 := by omega
  rw [e, mul_comm (fibonacciFactorial n) (fibonacciFactorial (n + 2))]

end
end MetaMathlibExt
