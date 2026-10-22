/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Real.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
import Mathlib.Algebra.Order.Archimedean.Real.Basic

@[expose] public section

open scoped BigOperators

namespace MetaMathlibExt

/--
**Binomial theorem for rising factorials.** For every natural number $n$ and all real numbers
$a$ and $b$, writing $x^{\overline{m}} = x(x+1)\cdots(x+m-1)$ for the rising factorial,
$$(a+b)^{\overline{n}} = \sum_{k=0}^{n} \binom{n}{k}\, a^{\overline{k}}\, b^{\overline{n-k}}.$$

Proves `Wanted` entry `ascPochhammer_eval_add`.

Source: Paul Eloe and Catherine Kublik,
"When Numerical Analysis Crosses Paths with Catalan and Generalized Motzkin Numbers,"
Journal of Integer Sequences 21 (2018), Article 18.8.4,
Theorem (label binomthm_risingpoly), equation (label `binomial theorem`),
lines 156–161,
https://cs.uwaterloo.ca/journals/JIS/VOL21/Kublik/kublik2.tex
-/
theorem ascPochhammer_eval_add (n : ℕ) (a b : ℝ) :
    (ascPochhammer ℝ n).eval (a + b) =
      ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
        (ascPochhammer ℝ k).eval a *
        (ascPochhammer ℝ (n - k)).eval b := by
  induction n generalizing a b with
  | zero => simp
  | succ n ih =>
    have hP : ∀ (m : ℕ) (x : ℝ),
        (ascPochhammer ℝ (m + 1)).eval x =
          (ascPochhammer ℝ m).eval x * (x + (m : ℝ)) :=
      fun m x => ascPochhammer_succ_eval m x
    rw [hP n (a + b), ih, Finset.sum_mul]
    -- Step B: each term splits into an A-part and a B-part
    have eAB : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ k).eval a *
          (ascPochhammer ℝ (n - k)).eval b * (a + b + (n : ℝ)))
        = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ k).eval a *
          (ascPochhammer ℝ (n + 1 - k)).eval b)
        + (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n - k)).eval b) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hk_le : k ≤ n := by
        have := Finset.mem_range.mp hk
        omega
      have hkn : ((n - k : ℕ) : ℝ) + (k : ℝ) = (n : ℝ) := by
        exact_mod_cast Nat.sub_add_cancel hk_le
      have hPb : (ascPochhammer ℝ (n + 1 - k)).eval b
          = (ascPochhammer ℝ (n - k)).eval b * (b + ((n - k : ℕ) : ℝ)) := by
        have hsub : n + 1 - k = (n - k) + 1 := by omega
        rw [hsub]
        exact ascPochhammer_succ_eval (n - k) b
      have hPa : (ascPochhammer ℝ (k + 1)).eval a
          = (ascPochhammer ℝ k).eval a * (a + (k : ℝ)) :=
        ascPochhammer_succ_eval k a
      have hs : a + b + (n : ℝ)
          = (b + ((n - k : ℕ) : ℝ)) + (a + (k : ℝ)) := by
        rw [← hkn]; ring
      rw [hPb, hPa, hs]; ring
    rw [eAB]
    -- Step C: recombine via the Pascal recurrence
    have e1 : (∑ k ∈ Finset.range (n + 1 + 1), ((n + 1).choose k : ℝ) *
          (ascPochhammer ℝ k).eval a *
          (ascPochhammer ℝ (n + 1 - k)).eval b)
        = (∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n + 1 - (k + 1))).eval b)
        + ((n + 1).choose 0 : ℝ) *
          (ascPochhammer ℝ 0).eval a *
          (ascPochhammer ℝ (n + 1 - 0)).eval b :=
      Finset.sum_range_succ' _ _
    have eT : (∑ k ∈ Finset.range (n + 1), ((n + 1).choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n + 1 - (k + 1))).eval b)
        = (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n - k)).eval b)
        + (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n - k)).eval b) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k hk
      have hC : (((n + 1).choose (k + 1) : ℕ) : ℝ)
          = (n.choose k : ℝ) + (n.choose (k + 1) : ℝ) := by
        rw [Nat.choose_succ_succ', Nat.cast_add]
      have hsub : n + 1 - (k + 1) = n - k := by omega
      rw [hsub, hC, add_mul, add_mul]
    have e3 : (∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
          (ascPochhammer ℝ k).eval a *
          (ascPochhammer ℝ (n + 1 - k)).eval b)
        = (∑ k ∈ Finset.range n, (n.choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n + 1 - (k + 1))).eval b)
        + (n.choose 0 : ℝ) *
          (ascPochhammer ℝ 0).eval a *
          (ascPochhammer ℝ (n + 1 - 0)).eval b :=
      Finset.sum_range_succ' _ _
    have eAsh : (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n - k)).eval b)
        = (∑ k ∈ Finset.range n, (n.choose (k + 1) : ℝ) *
          (ascPochhammer ℝ (k + 1)).eval a *
          (ascPochhammer ℝ (n + 1 - (k + 1))).eval b) + 0 := by
      have epeel : (∑ k ∈ Finset.range (n + 1), (n.choose (k + 1) : ℝ) *
            (ascPochhammer ℝ (k + 1)).eval a *
            (ascPochhammer ℝ (n - k)).eval b)
          = (∑ k ∈ Finset.range n, (n.choose (k + 1) : ℝ) *
            (ascPochhammer ℝ (k + 1)).eval a *
            (ascPochhammer ℝ (n - k)).eval b)
          + (n.choose (n + 1) : ℝ) *
            (ascPochhammer ℝ (n + 1)).eval a *
            (ascPochhammer ℝ (n - n)).eval b :=
        Finset.sum_range_succ _ _
      rw [epeel]
      congr 1
      · apply Finset.sum_congr rfl
        intro k hk
        have hsub : n + 1 - (k + 1) = n - k := by
          have := Finset.mem_range.mp hk
          omega
        rw [hsub]
      · have h0 : n.choose (n + 1) = 0 :=
          Nat.choose_eq_zero_of_lt (Nat.lt_succ_self n)
        rw [h0]
        simp
    have hT0 : ((n + 1).choose 0 : ℝ) *
          (ascPochhammer ℝ 0).eval a *
          (ascPochhammer ℝ (n + 1 - 0)).eval b
        = (n.choose 0 : ℝ) *
          (ascPochhammer ℝ 0).eval a *
          (ascPochhammer ℝ (n + 1 - 0)).eval b := by
      simp
    rw [e1, eT, eAsh, hT0, e3, add_zero]
    ring

end MetaMathlibExt
