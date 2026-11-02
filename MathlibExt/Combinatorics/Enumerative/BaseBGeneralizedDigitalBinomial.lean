/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Nat.Factorial.Basic
public import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import MathlibExt.Algebra.Polynomial.RisingFactorialBinomial

@[expose] public section

namespace MetaMathlibExt

private theorem riseFact_vandermonde (d : ℕ) (x y : ℝ) :
    (∏ j ∈ Finset.range d, (x + y + (j : ℝ))) / (d.factorial : ℝ) =
    ∑ k ∈ Finset.range (d + 1),
      (((∏ j ∈ Finset.range k, (x + (j : ℝ))) / (k.factorial : ℝ)) *
      ((∏ j ∈ Finset.range (d - k), (y + (j : ℝ))) / ((d - k).factorial : ℝ))) := by
  have hP : ∀ (z : ℝ) (t : ℕ),
      ∏ j ∈ Finset.range t, (z + (j : ℝ)) = (ascPochhammer ℝ t).eval z := by
    intro z t
    induction t with
    | zero => simp
    | succ t ih => rw [Finset.prod_range_succ, ih, ascPochhammer_succ_eval]
  simp only [hP]
  rw [ascPochhammer_eval_add, Finset.sum_div]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hkd : k ≤ d := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have hc : (d.choose k : ℝ) ≠ 0 := by exact_mod_cast (Nat.choose_pos hkd).ne'
  rw [← Nat.choose_mul_factorial_mul_factorial hkd]
  push_cast
  field_simp

private theorem digit_recon (b N m : ℕ) (hb : 2 ≤ b) (hm : m < b ^ N) :
    ∑ i ∈ Finset.range N, (m / b ^ i % b) * b ^ i = m := by
  induction N generalizing m with
  | zero =>
    rw [pow_zero] at hm
    have hm0 : m = 0 := by omega
    subst hm0
    simp
  | succ N ih =>
    have hbpos : 0 < b := by omega
    have hdiv : m / b < b ^ N := by
      have h1 : m < b ^ N * b := by
        have hps := pow_succ b N
        omega
      exact (Nat.div_lt_iff_lt_mul hbpos).mpr h1
    have step := ih (m / b) hdiv
    have hsplit := Finset.sum_range_succ' (fun i => (m / b ^ i % b) * b ^ i) N
    rw [hsplit]
    have h0 : (m / b ^ 0 % b) * b ^ 0 = m % b := by simp
    have hterm : ∀ i ∈ Finset.range N,
        (m / b ^ (i + 1) % b) * b ^ (i + 1) = b * (((m / b) / b ^ i % b) * b ^ i) := by
      intro i _
      have e1 : m / b ^ (i + 1) = (m / b) / b ^ i := by
        have hbi : b ^ (i + 1) = b * b ^ i := pow_succ' b i
        rw [hbi, ← Nat.div_div_eq_div_mul]
      rw [e1, pow_succ]
      ring
    have hS : (∑ i ∈ Finset.range N, (m / b ^ (i + 1) % b) * b ^ (i + 1))
        = b * (∑ i ∈ Finset.range N, (((m / b) / b ^ i % b) * b ^ i)) := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun i hi => hterm i hi)
    rw [hS, h0, step, add_comm]
    exact Nat.mod_add_div m b

private theorem digit_ofSum (b N : ℕ) (t : ℕ → ℕ) (hb : 2 ≤ b)
    (ht : ∀ i ∈ Finset.range N, t i < b) :
    ∀ i ∈ Finset.range N, (∑ j ∈ Finset.range N, t j * b ^ j) / b ^ i % b = t i := by
  induction N generalizing t with
  | zero =>
    intro i hi
    have hlt : i < 0 := Finset.mem_range.mp hi
    omega
  | succ N ih =>
    intro i hi
    have hbpos : 0 < b := by omega
    have hS : (∑ j ∈ Finset.range (N + 1), t j * b ^ j)
        = t 0 + b * (∑ j ∈ Finset.range N, t (j + 1) * b ^ j) := by
      have hsplit := Finset.sum_range_succ' (fun j => t j * b ^ j) N
      rw [hsplit]
      have h0 : t 0 * b ^ 0 = t 0 := by simp
      have hterm : ∀ j ∈ Finset.range N,
          t (j + 1) * b ^ (j + 1) = b * (t (j + 1) * b ^ j) := by
        intro j _
        rw [pow_succ]
        ring
      have hS2 : (∑ j ∈ Finset.range N, t (j + 1) * b ^ (j + 1))
          = b * (∑ j ∈ Finset.range N, t (j + 1) * b ^ j) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j hj => hterm j hj)
      rw [h0, hS2]
      ring
    have hiN1 : i < N + 1 := Finset.mem_range.mp hi
    by_cases hi0 : i = 0
    · subst hi0
      rw [pow_zero, Nat.div_one, hS, Nat.add_mul_mod_self_left]
      have ht0 : t 0 < b := ht 0 (Finset.mem_range.mpr (Nat.zero_lt_succ N))
      exact Nat.mod_eq_of_lt ht0
    · obtain ⟨k, hk_eq⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
      subst hk_eq
      have hkN : k < N := by
        have hmem : k + 1 < N + 1 := Finset.mem_range.mp hi
        omega
      have hkmem : k ∈ Finset.range N := Finset.mem_range.mpr hkN
      have ht0 : t 0 < b := ht 0 (Finset.mem_range.mpr (Nat.zero_lt_succ N))
      have hdiv : (∑ j ∈ Finset.range (N + 1), t j * b ^ j) / b ^ (k + 1)
          = (∑ j ∈ Finset.range N, t (j + 1) * b ^ j) / b ^ k := by
        rw [hS]
        have hdiv0 : (t 0 + b * (∑ j ∈ Finset.range N, t (j + 1) * b ^ j)) / b
            = (∑ j ∈ Finset.range N, t (j + 1) * b ^ j) := by
          rw [Nat.add_mul_div_left _ _ hbpos, Nat.div_eq_of_lt ht0, Nat.zero_add]
        have hbk : b ^ (k + 1) = b * b ^ k := pow_succ' b k
        rw [hbk, ← Nat.div_div_eq_div_mul, hdiv0]
      rw [hdiv]
      have ht' : ∀ j ∈ Finset.range N, t (j + 1) < b := by
        intro j hj
        have hjN : j < N := Finset.mem_range.mp hj
        exact ht (j + 1) (Finset.mem_range.mpr (by omega))
      exact ih (fun j => t (j + 1)) ht' k hkmem

private theorem tuple_digit_le (b N n : ℕ)
    (x_ : (i : Fin N) → Fin (n / b ^ i.val % b + 1)) (i : ℕ) (hi : i < N) :
    (x_ ⟨i, hi⟩).val ≤ n / b ^ i % b :=
  Nat.le_of_lt_succ (x_ ⟨i, hi⟩).isLt

private theorem tuple_digit_lt (b N n : ℕ) (hb : 2 ≤ b)
    (x_ : (i : Fin N) → Fin (n / b ^ i.val % b + 1)) (i : ℕ) (hi : i < N) :
    (x_ ⟨i, hi⟩).val < b := by
  have hbpos : 0 < b := by omega
  exact lt_of_le_of_lt (tuple_digit_le b N n x_ i hi) (Nat.mod_lt _ hbpos)

/-- **Base-$b$ generalized digital binomial theorem.** Let $b \ge 2$, let $N$ and $n$ be natural
numbers with $n < b^N$, and let $x$ and $y$ be real numbers. For a natural number $m$ write
$m_i = \lfloor m / b^i \rfloor \bmod b$ for its $i$-th base-$b$ digit, and write
$z^{\overline{j}} = z(z+1)\cdots(z+j-1)$ for the rising factorial. Then
$$\prod_{i=0}^{N-1} \frac{(x+y)^{\overline{n_i}}}{n_i!} = \sum_{m} \left(\prod_{i=0}^{N-1}
\frac{x^{\overline{m_i}}}{m_i!}\right) \left(\prod_{i=0}^{N-1}
\frac{y^{\overline{(n-m)_i}}}{(n-m)_i!}\right),$$
where the sum runs over the natural numbers $m \le n$ with $m_i \le n_i$ for every $i < N$.

Proves `Wanted` entry `base_b_generalized_digital_binomial_theorem`.

Source: Hieu D. Nguyen, "A Generalization of the Digital Binomial
Theorem," Journal of Integer Sequences 18 (2015), Article 15.5.7,
Theorem (label th:digital-binomial-theorem-non-binary),
equation (eq:digital-binomial-theorem-non-binary), lines 122–127,
https://cs.uwaterloo.ca/journals/JIS/VOL18/Nguyen/nguyen6.tex
-/
theorem base_b_generalized_digital_binomial_theorem
    (b N n : ℕ) (x y : ℝ) (hb : 2 ≤ b) (hn : n < b ^ N) :
    (∏ i ∈ Finset.range N,
      ((∏ j ∈ Finset.range (n / b ^ i % b), (x + y + (j : ℝ))) /
        ((n / b ^ i % b).factorial : ℝ)) =
      ∑ m ∈ Finset.filter
        (fun m => ∀ i ∈ Finset.range N, m / b ^ i % b ≤ n / b ^ i % b)
        (Finset.range (n + 1)),
        ((∏ i ∈ Finset.range N,
          ((∏ j ∈ Finset.range (m / b ^ i % b), (x + (j : ℝ))) /
            ((m / b ^ i % b).factorial : ℝ))) *
          (∏ i ∈ Finset.range N,
            ((∏ j ∈ Finset.range ((n - m) / b ^ i % b), (y + (j : ℝ))) /
              (((n - m) / b ^ i % b).factorial : ℝ))))) := by
  have hbpos : 0 < b := by omega
  have hdig_lt : ∀ i : ℕ, n / b ^ i % b < b := fun i => Nat.mod_lt _ hbpos
  have hdig : ∀ i ∈ Finset.range N,
      (∏ j ∈ Finset.range (n / b ^ i % b), (x + y + (j : ℝ))) /
        ((n / b ^ i % b).factorial : ℝ) =
      ∑ k ∈ Finset.range (n / b ^ i % b + 1),
        (((∏ j ∈ Finset.range k, (x + (j : ℝ))) / (k.factorial : ℝ)) *
        ((∏ j ∈ Finset.range (n / b ^ i % b - k), (y + (j : ℝ))) /
          ((n / b ^ i % b - k).factorial : ℝ))) :=
    fun i _ => riseFact_vandermonde _ x y
  have hLHS : (∏ i ∈ Finset.range N,
        ((∏ j ∈ Finset.range (n / b ^ i % b), (x + y + (j : ℝ))) /
          ((n / b ^ i % b).factorial : ℝ)))
      = ∏ i ∈ Finset.range N,
        ∑ k ∈ Finset.range (n / b ^ i % b + 1),
        (((∏ j ∈ Finset.range k, (x + (j : ℝ))) / (k.factorial : ℝ)) *
        ((∏ j ∈ Finset.range (n / b ^ i % b - k), (y + (j : ℝ))) /
          ((n / b ^ i % b - k).factorial : ℝ))) :=
    Finset.prod_congr rfl hdig
  have hFin : ∀ i : Fin N,
      (∑ k ∈ Finset.range (n / b ^ i.val % b + 1),
        (((∏ l ∈ Finset.range k, (x + (l : ℝ))) / (k.factorial : ℝ)) *
        ((∏ l ∈ Finset.range (n / b ^ i.val % b - k), (y + (l : ℝ))) /
          ((n / b ^ i.val % b - k).factorial : ℝ))))
      = ∑ j : Fin (n / b ^ i.val % b + 1),
        (((∏ l ∈ Finset.range (j.val), (x + (l : ℝ))) / ((j.val).factorial : ℝ)) *
        ((∏ l ∈ Finset.range (n / b ^ i.val % b - j.val), (y + (l : ℝ))) /
          ((n / b ^ i.val % b - j.val).factorial : ℝ))) := by
    intro i
    exact (Fin.sum_univ_eq_sum_range _ _).symm
  have hFinProd : (∏ i ∈ Finset.range N,
        ∑ k ∈ Finset.range (n / b ^ i % b + 1),
        (((∏ l ∈ Finset.range k, (x + (l : ℝ))) / (k.factorial : ℝ)) *
        ((∏ l ∈ Finset.range (n / b ^ i % b - k), (y + (l : ℝ))) /
          ((n / b ^ i % b - k).factorial : ℝ))))
      = ∏ i : Fin N, ∑ j : Fin (n / b ^ i.val % b + 1),
        (((∏ l ∈ Finset.range (j.val), (x + (l : ℝ))) / ((j.val).factorial : ℝ)) *
        ((∏ l ∈ Finset.range (n / b ^ i.val % b - j.val), (y + (l : ℝ))) /
          ((n / b ^ i.val % b - j.val).factorial : ℝ))) := by
    rw [← Fin.prod_univ_eq_prod_range _ N]
    exact Finset.prod_congr rfl (fun i _ => hFin i)
  have hmid : (∏ i : Fin N, ∑ j : Fin (n / b ^ i.val % b + 1),
        (((∏ l ∈ Finset.range (j.val), (x + (l : ℝ))) / ((j.val).factorial : ℝ)) *
        ((∏ l ∈ Finset.range (n / b ^ i.val % b - j.val), (y + (l : ℝ))) /
          ((n / b ^ i.val % b - j.val).factorial : ℝ))))
      = ∑ x_ : ((i : Fin N) → Fin (n / b ^ i.val % b + 1)), ∏ i : Fin N,
        (((∏ l ∈ Finset.range ((x_ i).val), (x + (l : ℝ))) / (((x_ i).val).factorial : ℝ)) *
        ((∏ l ∈ Finset.range (n / b ^ i.val % b - (x_ i).val), (y + (l : ℝ))) /
          ((n / b ^ i.val % b - (x_ i).val).factorial : ℝ))) :=
    Fintype.prod_sum _
  rw [hLHS, hFinProd, hmid]
  refine Finset.sum_bij (fun x_ _ => ∑ i ∈ Finset.range N,
    (if h : i < N then (x_ ⟨i, h⟩).val else 0) * b ^ i) ?_ ?_ ?_ ?_
  · -- forward map lands in filter set
    intro x_ _
    show (∑ i ∈ Finset.range N, (if h : i < N then (x_ ⟨i, h⟩).val else 0) * b ^ i)
      ∈ Finset.filter (fun m => ∀ i ∈ Finset.range N, m / b ^ i % b ≤ n / b ^ i % b)
        (Finset.range (n + 1))
    have he_le : ∀ i ∈ Finset.range N,
        (if h : i < N then (x_ ⟨i, h⟩).val else 0) ≤ n / b ^ i % b := by
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      rw [dite_eq_left hiN]
      exact tuple_digit_le b N n x_ i hiN
    have he_lt : ∀ i ∈ Finset.range N,
        (if h : i < N then (x_ ⟨i, h⟩).val else 0) < b := by
      intro i hi
      exact lt_of_le_of_lt (he_le i hi) (hdig_lt i)
    have hle : (∑ i ∈ Finset.range N, (if h : i < N then (x_ ⟨i, h⟩).val else 0) * b ^ i) ≤ n := by
      have h1 : (∑ i ∈ Finset.range N, (if h : i < N then (x_ ⟨i, h⟩).val else 0) * b ^ i)
          ≤ ∑ i ∈ Finset.range N, (n / b ^ i % b) * b ^ i := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right (he_le i hi) (Nat.zero_le _)
      have h2 : (∑ i ∈ Finset.range N, (n / b ^ i % b) * b ^ i) = n :=
        digit_recon b N n hb hn
      omega
    have hdig_eq : ∀ i ∈ Finset.range N,
        (∑ j ∈ Finset.range N, (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j) / b ^ i % b
        = (if h : i < N then (x_ ⟨i, h⟩).val else 0) :=
      fun i hi => digit_ofSum b N _ hb he_lt i hi
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_range.mpr (by omega), ?_⟩
    intro i hi
    rw [hdig_eq i hi]
    exact he_le i hi
  · -- forward map is injective
    intro x1 _ x2 _ heq
    have heq' : (∑ i ∈ Finset.range N, (if h : i < N then (x1 ⟨i, h⟩).val else 0) * b ^ i)
        = (∑ i ∈ Finset.range N, (if h : i < N then (x2 ⟨i, h⟩).val else 0) * b ^ i) := heq
    have he_lt1 : ∀ i ∈ Finset.range N, (if h : i < N then (x1 ⟨i, h⟩).val else 0) < b := by
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      rw [dite_eq_left hiN]
      exact tuple_digit_lt b N n hb x1 i hiN
    have he_lt2 : ∀ i ∈ Finset.range N, (if h : i < N then (x2 ⟨i, h⟩).val else 0) < b := by
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      rw [dite_eq_left hiN]
      exact tuple_digit_lt b N n hb x2 i hiN
    have d1 : ∀ i ∈ Finset.range N,
        (∑ j ∈ Finset.range N, (if h : j < N then (x1 ⟨j, h⟩).val else 0) * b ^ j) / b ^ i % b
        = (if h : i < N then (x1 ⟨i, h⟩).val else 0) :=
      fun i hi => digit_ofSum b N _ hb he_lt1 i hi
    have d2 : ∀ i ∈ Finset.range N,
        (∑ j ∈ Finset.range N, (if h : j < N then (x2 ⟨j, h⟩).val else 0) * b ^ j) / b ^ i % b
        = (if h : i < N then (x2 ⟨i, h⟩).val else 0) :=
      fun i hi => digit_ofSum b N _ hb he_lt2 i hi
    apply funext
    intro i
    apply Fin.ext
    have hiR : i.val ∈ Finset.range N := Finset.mem_range.mpr i.isLt
    have g1 : (if h : i.val < N then (x1 ⟨i.val, h⟩).val else 0) = (x1 i).val := by
      rw [dite_eq_left i.isLt]
    have g2 : (if h : i.val < N then (x2 ⟨i.val, h⟩).val else 0) = (x2 i).val := by
      rw [dite_eq_left i.isLt]
    have e1 := d1 i.val hiR
    have e2 := d2 i.val hiR
    rw [heq'] at e1
    have hboth : (if h : i.val < N then (x1 ⟨i.val, h⟩).val else 0)
        = (if h : i.val < N then (x2 ⟨i.val, h⟩).val else 0) := by
      rw [← e1, e2]
    rw [g1] at hboth
    rw [g2] at hboth
    exact hboth
  · -- forward map is surjective
    intro m hm
    have hmF := Finset.mem_filter.mp hm
    have hmle : m ≤ n := by
      have hmem : m < n + 1 := Finset.mem_range.mp hmF.1
      omega
    have hmN : m < b ^ N := lt_of_le_of_lt hmle hn
    let xtup : (i : Fin N) → Fin (n / b ^ i.val % b + 1) :=
      fun i => ⟨m / b ^ i.val % b, Nat.lt_succ_of_le (hmF.2 i.val (Finset.mem_range.mpr i.isLt))⟩
    refine ⟨xtup, Finset.mem_univ _, ?_⟩
    show (∑ i ∈ Finset.range N, (if h : i < N then (xtup ⟨i, h⟩).val else 0) * b ^ i) = m
    have hcongr2 : (∑ i ∈ Finset.range N, (if h : i < N then (xtup ⟨i, h⟩).val else 0) * b ^ i)
        = ∑ i ∈ Finset.range N, (m / b ^ i % b) * b ^ i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [dite_eq_left (Finset.mem_range.mp hi)]
    rw [hcongr2]
    exact digit_recon b N m hb hmN
  · -- summands match
    intro x_ _
    show (∏ i : Fin N,
        (((∏ l ∈ Finset.range ((x_ i).val), (x + (l : ℝ))) / (((x_ i).val).factorial : ℝ)) *
        ((∏ l ∈ Finset.range (n / b ^ i.val % b - (x_ i).val), (y + (l : ℝ))) /
          ((n / b ^ i.val % b - (x_ i).val).factorial : ℝ))))
      = (((∏ i ∈ Finset.range N,
        ((∏ l ∈ Finset.range (((∑ j ∈ Finset.range N,
            (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j) / b ^ i % b)), (x + (l : ℝ))) /
          (((((∑ j ∈ Finset.range N,
            (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j) / b ^ i % b)).factorial : ℕ) :
              ℝ))) *
        (∏ i ∈ Finset.range N,
        ((∏ l ∈ Finset.range (((n - (∑ j ∈ Finset.range N,
            (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j)) / b ^ i % b)), (y + (l : ℝ))) /
          (((((n - (∑ j ∈ Finset.range N,
            (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j)) / b ^ i % b)).factorial : ℕ) :
              ℝ)))))
    have he_le : ∀ i ∈ Finset.range N,
        (if h : i < N then (x_ ⟨i, h⟩).val else 0) ≤ n / b ^ i % b := by
      intro i hi
      have hiN : i < N := Finset.mem_range.mp hi
      rw [dite_eq_left hiN]
      exact tuple_digit_le b N n x_ i hiN
    have he_lt : ∀ i ∈ Finset.range N,
        (if h : i < N then (x_ ⟨i, h⟩).val else 0) < b := by
      intro i hi
      exact lt_of_le_of_lt (he_le i hi) (hdig_lt i)
    have hsub : ∀ i ∈ Finset.range N,
        (n - (∑ j ∈ Finset.range N, (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j)) / b ^ i % b
        = n / b ^ i % b - (if h : i < N then (x_ ⟨i, h⟩).val else 0) := by
      have hadd : (∑ i ∈ Finset.range N, ((n / b ^ i % b
          - (if h : i < N then (x_ ⟨i, h⟩).val else 0))) * b ^ i)
          + (∑ i ∈ Finset.range N, (if h : i < N then (x_ ⟨i, h⟩).val else 0) * b ^ i)
          = n := by
        have hstep : (∑ i ∈ Finset.range N, ((n / b ^ i % b
            - (if h : i < N then (x_ ⟨i, h⟩).val else 0))) * b ^ i)
            + (∑ i ∈ Finset.range N, (if h : i < N then (x_ ⟨i, h⟩).val else 0) * b ^ i)
            = (∑ i ∈ Finset.range N, (n / b ^ i % b) * b ^ i) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i hi
          rw [← add_mul, Nat.sub_add_cancel (he_le i hi)]
        rw [hstep]
        exact digit_recon b N n hb hn
      have hnm : n - (∑ i ∈ Finset.range N, (if h : i < N then (x_ ⟨i, h⟩).val else 0) * b ^ i)
          = (∑ i ∈ Finset.range N, ((n / b ^ i % b
            - (if h : i < N then (x_ ⟨i, h⟩).val else 0))) * b ^ i) := by
        omega
      intro i hi
      rw [hnm]
      have hbnd : ∀ j ∈ Finset.range N,
          (n / b ^ j % b - (if h : j < N then (x_ ⟨j, h⟩).val else 0)) < b := by
        intro j hj
        exact lt_of_le_of_lt (Nat.sub_le _ _) (hdig_lt j)
      exact digit_ofSum b N _ hb hbnd i hi
    have dm : ∀ i ∈ Finset.range N,
        (∑ j ∈ Finset.range N, (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j) / b ^ i % b
        = (if h : i < N then (x_ ⟨i, h⟩).val else 0) :=
      fun i hi => digit_ofSum b N _ hb he_lt i hi
    have idx : ∀ i : Fin N, (x_ i).val
        = (if h : i.val < N then (x_ ⟨i.val, h⟩).val else 0) := by
      intro i
      rw [dite_eq_left i.isLt]
    have c1 : (∏ i : Fin N,
          ((∏ l ∈ Finset.range ((x_ i).val), (x + (l : ℝ))) / (((x_ i).val).factorial : ℝ)))
        = ∏ i ∈ Finset.range N,
          ((∏ l ∈ Finset.range ((if h : i < N then (x_ ⟨i, h⟩).val else 0)), (x + (l : ℝ))) /
            ((((if h : i < N then (x_ ⟨i, h⟩).val else 0)).factorial : ℕ) : ℝ)) := by
      rw [← Fin.prod_univ_eq_prod_range _ N]
      apply Finset.prod_congr rfl
      intro i _
      rw [idx i]
    have c2 : (∏ i : Fin N,
          ((∏ l ∈ Finset.range (n / b ^ i.val % b - (x_ i).val), (y + (l : ℝ))) /
            ((n / b ^ i.val % b - (x_ i).val).factorial : ℝ)))
        = ∏ i ∈ Finset.range N,
          ((∏ l ∈ Finset.range (n / b ^ i % b
            - (if h : i < N then (x_ ⟨i, h⟩).val else 0)), (y + (l : ℝ))) /
            (((n / b ^ i % b - (if h : i < N then (x_ ⟨i, h⟩).val else 0)).factorial : ℕ) :
              ℝ)) := by
      rw [← Fin.prod_univ_eq_prod_range _ N]
      apply Finset.prod_congr rfl
      intro i _
      rw [idx i]
    have cx : (∏ i ∈ Finset.range N,
          ((∏ l ∈ Finset.range ((∑ j ∈ Finset.range N,
            (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j) / b ^ i % b), (x + (l : ℝ))) /
            (((((∑ j ∈ Finset.range N,
              (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j) / b ^ i % b)).factorial : ℕ) :
                ℝ)))
        = ∏ i ∈ Finset.range N,
          ((∏ l ∈ Finset.range ((if h : i < N then (x_ ⟨i, h⟩).val else 0)), (x + (l : ℝ))) /
            ((((if h : i < N then (x_ ⟨i, h⟩).val else 0)).factorial : ℕ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [dm i hi]
    have cy : (∏ i ∈ Finset.range N,
          ((∏ l ∈ Finset.range (((n - (∑ j ∈ Finset.range N,
            (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j)) / b ^ i % b)), (y + (l : ℝ))) /
            (((((n - (∑ j ∈ Finset.range N,
              (if h : j < N then (x_ ⟨j, h⟩).val else 0) * b ^ j)) / b ^ i % b)).factorial : ℕ) :
                ℝ)))
        = ∏ i ∈ Finset.range N,
          ((∏ l ∈ Finset.range (n / b ^ i % b
            - (if h : i < N then (x_ ⟨i, h⟩).val else 0)), (y + (l : ℝ))) /
            (((n / b ^ i % b - (if h : i < N then (x_ ⟨i, h⟩).val else 0)).factorial : ℕ) :
              ℝ)) := by
      apply Finset.prod_congr rfl
      intro i hi
      rw [hsub i hi]
    rw [Finset.prod_mul_distrib, c1, c2, ← cx, ← cy]

end MetaMathlibExt
