/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Real.Basic
public import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Algebra.Field.GeomSum
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 6, Entry 16

Finite sum of rᵏ/(1-axᵏ) splits into two partial-fraction-type sums.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch6

namespace Entry16FiniteSum

open scoped Nat Real BigOperators Interval
open Finset

noncomputable section

/-- Finite geometric sum over `Icc 1 m` with shifted exponent. -/
private theorem entry16_sum_Icc_pow_pred {K : Type*} [Semiring K] (z : K) (m : ℕ) :
    ∑ k ∈ Icc 1 m, z ^ (k - 1) = ∑ i ∈ range m, z ^ i := by
  induction m with
  | zero =>
    rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 from by omega)]
    simp
  | succ m ih =>
    have h1 : ∑ k ∈ Icc 1 (m + 1), z ^ (k - 1)
        = (∑ k ∈ Icc 1 m, z ^ (k - 1)) + z ^ (m + 1 - 1) :=
      sum_Icc_succ_top (show (1 : ℕ) ≤ m + 1 by omega) _
    rw [h1, ih, sum_range_succ, Nat.add_sub_cancel]

/-- Ramanujan, Part I, Chapter 6, Entry 16, finite form (induction generalisation). -/
private theorem entry16_aux_identity {K : Type*} [Field K] (a r x : K) : ∀ (m : ℕ),
    (∀ k ∈ Icc 1 m, 1 - a * x ^ k ≠ 0) →
    (∀ k ∈ Icc 1 m, 1 - r * x ^ (k - 1) ≠ 0) →
    ∑ k ∈ Icc 1 m, r ^ k / (1 - a * x ^ k) =
      (∑ k ∈ Icc 1 m, (a * r * x ^ k) ^ k / (1 - a * x ^ k)) +
      ∑ k ∈ Icc 1 m,
        a ^ (k - 1) *
          ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (m + 1)) /
            (1 - r * x ^ (k - 1)) := by
  intro m
  induction m with
  | zero =>
    intro _ _
    rw [Finset.Icc_eq_empty (show ¬ (1 : ℕ) ≤ 0 from by omega)]
    simp
  | succ m ih =>
    intro haxm hrxm
    have sub1 : ∀ k ∈ Icc 1 m, k ∈ Icc 1 (m + 1) := by
      intro k hk
      simp only [Finset.mem_Icc] at hk ⊢
      exact ⟨hk.1, Nat.le_succ_of_le hk.2⟩
    have hmem_top : m + 1 ∈ Icc 1 (m + 1) :=
      Finset.mem_Icc.mpr ⟨by omega, le_rfl⟩
    have haxm_top : 1 - a * x ^ (m + 1) ≠ 0 := haxm (m + 1) hmem_top
    have hz : a * x ^ (m + 1) ≠ 1 := by
      intro h
      exact haxm_top (by rw [h, sub_self])
    have hz1 : a * x ^ (m + 1) - 1 ≠ 0 := sub_ne_zero.mpr hz
    have hL : ∑ k ∈ Icc 1 (m + 1), r ^ k / (1 - a * x ^ k)
        = (∑ k ∈ Icc 1 m, r ^ k / (1 - a * x ^ k))
          + r ^ (m + 1) / (1 - a * x ^ (m + 1)) :=
      sum_Icc_succ_top (show (1 : ℕ) ≤ m + 1 by omega) _
    have hM : ∑ k ∈ Icc 1 (m + 1), (a * r * x ^ k) ^ k / (1 - a * x ^ k)
        = (∑ k ∈ Icc 1 m, (a * r * x ^ k) ^ k / (1 - a * x ^ k))
          + (a * r * x ^ (m + 1)) ^ (m + 1) / (1 - a * x ^ (m + 1)) :=
      sum_Icc_succ_top (show (1 : ℕ) ≤ m + 1 by omega) _
    have hRsplit :
        (∑ k ∈ Icc 1 (m + 1),
          a ^ (k - 1) *
            ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (m + 1 + 1)) /
              (1 - r * x ^ (k - 1)))
        = (∑ k ∈ Icc 1 m,
          a ^ (k - 1) *
            ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (m + 1 + 1)) /
              (1 - r * x ^ (k - 1)))
          + a ^ (m + 1 - 1) *
            ((r * x ^ (m + 1 - 1)) ^ (m + 1)
              - (r * x ^ (m + 1 - 1)) ^ (m + 1 + 1)) /
              (1 - r * x ^ (m + 1 - 1)) :=
      sum_Icc_succ_top (show (1 : ℕ) ≤ m + 1 by omega) _
    have hSsplit :
        (∑ k ∈ Icc 1 (m + 1), a ^ (k - 1) * (r * x ^ (k - 1)) ^ (m + 1))
        = (∑ k ∈ Icc 1 m, a ^ (k - 1) * (r * x ^ (k - 1)) ^ (m + 1))
          + a ^ (m + 1 - 1) * (r * x ^ (m + 1 - 1)) ^ (m + 1) :=
      sum_Icc_succ_top (show (1 : ℕ) ≤ m + 1 by omega) _
    have hdiff : ∀ k ∈ Icc 1 m,
        a ^ (k - 1) *
          ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (m + 1 + 1)) /
            (1 - r * x ^ (k - 1))
        = a ^ (k - 1) *
          ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (m + 1)) /
            (1 - r * x ^ (k - 1))
          + a ^ (k - 1) * (r * x ^ (k - 1)) ^ (m + 1) := by
      intro k hk
      have h1y : (1 : K) - r * x ^ (k - 1) ≠ 0 := hrxm k (sub1 k hk)
      have hps : (r * x ^ (k - 1)) ^ (m + 1 + 1)
          = (r * x ^ (k - 1)) ^ (m + 1) * (r * x ^ (k - 1)) :=
        pow_succ _ _
      rw [hps]
      field_simp [h1y]
      ring
    have hsum :
        (∑ k ∈ Icc 1 m,
          a ^ (k - 1) *
            ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (m + 1 + 1)) /
              (1 - r * x ^ (k - 1)))
        = (∑ k ∈ Icc 1 m,
          a ^ (k - 1) *
            ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (m + 1)) /
              (1 - r * x ^ (k - 1)))
          + (∑ k ∈ Icc 1 m, a ^ (k - 1) * (r * x ^ (k - 1)) ^ (m + 1)) := by
      rw [← sum_add_distrib]
      exact sum_congr rfl hdiff
    have hlast :
        a ^ (m + 1 - 1) *
          ((r * x ^ (m + 1 - 1)) ^ (m + 1)
            - (r * x ^ (m + 1 - 1)) ^ (m + 1 + 1)) /
            (1 - r * x ^ (m + 1 - 1))
        = a ^ (m + 1 - 1) * (r * x ^ (m + 1 - 1)) ^ (m + 1) := by
      have h1y : (1 : K) - r * x ^ (m + 1 - 1) ≠ 0 := hrxm (m + 1) hmem_top
      have hps : (r * x ^ (m + 1 - 1)) ^ (m + 1 + 1)
          = (r * x ^ (m + 1 - 1)) ^ (m + 1) * (r * x ^ (m + 1 - 1)) :=
        pow_succ _ _
      rw [hps]
      field_simp [h1y]
    have hR :
        (∑ k ∈ Icc 1 (m + 1),
          a ^ (k - 1) *
            ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (m + 1 + 1)) /
              (1 - r * x ^ (k - 1)))
        = (∑ k ∈ Icc 1 m,
          a ^ (k - 1) *
            ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (m + 1)) /
              (1 - r * x ^ (k - 1)))
          + (∑ k ∈ Icc 1 (m + 1),
            a ^ (k - 1) * (r * x ^ (k - 1)) ^ (m + 1)) := by
      rw [hRsplit, hsum, hlast, hSsplit]
      abel
    have hterm : ∀ k ∈ Icc 1 (m + 1),
        a ^ (k - 1) * (r * x ^ (k - 1)) ^ (m + 1)
          = r ^ (m + 1) * (a * x ^ (m + 1)) ^ (k - 1) := by
      intro k _
      simp only [mul_pow, ← pow_mul, Nat.mul_comm (k - 1) (m + 1)]
      ring
    have hS : (∑ k ∈ Icc 1 (m + 1), a ^ (k - 1) * (r * x ^ (k - 1)) ^ (m + 1))
        = r ^ (m + 1) *
          (((a * x ^ (m + 1)) ^ (m + 1) - 1) / ((a * x ^ (m + 1)) - 1)) := by
      rw [Finset.sum_congr rfl hterm, ← mul_sum,
        entry16_sum_Icc_pow_pred (a * x ^ (m + 1)) (m + 1),
        geom_sum_eq hz (m + 1)]
    have hpow : (a * r * x ^ (m + 1)) ^ (m + 1)
        = r ^ (m + 1) * (a * x ^ (m + 1)) ^ (m + 1) := by
      simp only [mul_pow]
      ring
    have hfin : r ^ (m + 1) *
          (((a * x ^ (m + 1)) ^ (m + 1) - 1) / ((a * x ^ (m + 1)) - 1))
        = (r ^ (m + 1) - (a * r * x ^ (m + 1)) ^ (m + 1))
          / (1 - a * x ^ (m + 1)) := by
      rw [hpow]
      field_simp [hz1, haxm_top]
      ring
    have hfin2 : r ^ (m + 1) / (1 - a * x ^ (m + 1))
        = (a * r * x ^ (m + 1)) ^ (m + 1) / (1 - a * x ^ (m + 1))
          + (r ^ (m + 1) - (a * r * x ^ (m + 1)) ^ (m + 1))
            / (1 - a * x ^ (m + 1)) := by
      rw [hpow, ← add_div, add_sub_cancel]
    have ih' := ih (fun k hk => haxm k (sub1 k hk))
      (fun k hk => hrxm k (sub1 k hk))
    rw [hL, hM, ih', hR, hS, hfin, hfin2]
    abel

/-- **A finite identity for $\sum_k r^k/(1-ax^k)$ over a field.** Let $K$ be a field, let
$a, r, x \in K$ and let $n \ge 0$ be an integer. Suppose that $1 - a x^k \ne 0$ and
$1 - r x^{k-1} \ne 0$ for every integer $k$ with $1 \le k \le n$. Then
$\sum_{k=1}^{n} \frac{r^k}{1 - a x^k} = \sum_{k=1}^{n} \frac{(a r x^k)^k}{1 - a x^k} +
\sum_{k=1}^{n} \frac{a^{k-1} \left( (r x^{k-1})^k - (r x^{k-1})^{n+1} \right)}{1 - r x^{k-1}}$.
For $n = 0$ all three sums are empty. -/
theorem ramanujan_part1_ch6_entry16_finite_sum_general
    {K : Type*} [Field K] (a r x : K) (n : ℕ)
    (hax : ∀ k ∈ Icc 1 n, 1 - a * x ^ k ≠ 0)
    (hrx : ∀ k ∈ Icc 1 n, 1 - r * x ^ (k - 1) ≠ 0) :
    ∑ k ∈ Icc 1 n, r ^ k / (1 - a * x ^ k) =
      (∑ k ∈ Icc 1 n,
        (a * r * x ^ k) ^ k / (1 - a * x ^ k)) +
      ∑ k ∈ Icc 1 n,
        a ^ (k - 1) *
          ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (n + 1)) /
            (1 - r * x ^ (k - 1)) := by
  exact entry16_aux_identity a r x n hax hrx

set_option linter.unusedVariables false in
/-- **Ramanujan's finite identity for $\sum_k r^k/(1-ax^k)$.** Let $a, r, x$ be real numbers
and let $n$ be a positive integer. Suppose that $1 - a x^k \ne 0$ and $1 - r x^{k-1} \ne 0$ for
every integer $k$ with $1 \le k \le n$. Then
$\sum_{k=1}^{n} \frac{r^k}{1 - a x^k} = \sum_{k=1}^{n} \frac{(a r x^k)^k}{1 - a x^k} +
\sum_{k=1}^{n} \frac{a^{k-1} \left( (r x^{k-1})^k - (r x^{k-1})^{n+1} \right)}{1 - r x^{k-1}}$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 6.
It follows from `ramanujan_part1_ch6_entry16_finite_sum_general` with `K := ℝ`; the
hypothesis `hn` is unused and keeps the source's shape.
Proves `Wanted` entry `ramanujan_part1_ch6_entry16_harmonicasymptotic`.
-/
theorem ramanujan_part1_ch6_entry16_finite_sum
    (a r x : ℝ) (n : ℕ) (hn : 0 < n)
    (hax : ∀ k ∈ Icc 1 n, 1 - a * x ^ k ≠ 0)
    (hrx : ∀ k ∈ Icc 1 n, 1 - r * x ^ (k - 1) ≠ 0) :
    ∑ k ∈ Icc 1 n, r ^ k / (1 - a * x ^ k) =
      (∑ k ∈ Icc 1 n,
        (a * r * x ^ k) ^ k / (1 - a * x ^ k)) +
      ∑ k ∈ Icc 1 n,
        a ^ (k - 1) *
          ((r * x ^ (k - 1)) ^ k - (r * x ^ (k - 1)) ^ (n + 1)) /
            (1 - r * x ^ (k - 1)) :=
  by apply ramanujan_part1_ch6_entry16_finite_sum_general <;> assumption

end

end Entry16FiniteSum

end MathlibExt.Analysis.Ramanujan.Part1Ch6
