/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ComplementarySequences
import Mathlib.Tactic.Linarith

/-!
# Interleaving formula for complementary sequences with a large gap

The lower bound on the distance from the interleaving function to the next sequence value
rules out the first branch of the three-case interleaving formula.

## References

* Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
  Article A95, pp. 1–26, Section 2.2, Theorem 3 and Corollary 2.
* Joachim Lambek and Leo Moser, *Inverse and complementary sequences of natural numbers*,
  American Mathematical Monthly 61 (1954), no. 7, pp. 454–458. Wu credits this paper
  in Section 2.1 for the complementary-sequence iteration underlying the interleaving formula.
-/

namespace MetaMathlibExt

/-- **Interleaving formula when $f(m) - \alpha(m) \ge m$.** Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) \ge 1$ and $f(m + 1) \ge f(m) + m$ for all $m \ge 1$,
and for $n \ge 1$ let $f_P(n)$ be the $n$-th positive integer that is not a value $f(m)$ with
$m \ge 1$. Let $\alpha : \mathbb{N} \to \mathbb{R}$ satisfy $f(m - 1) \le \alpha(m) \le f(m)$ for
all $m \ge 2$, and let $h : \mathbb{N} \to \mathbb{N}$ satisfy $h(n) \ge 1$ and
$\alpha(h(n)) \le n < \alpha(h(n) + 1)$ for all $n \ge 1$.
Suppose moreover that $f(m) - \alpha(m) \ge m$ for all $m \ge 2$. Then for every $n \ge 1$,
$f_P(n) = n + h(n)$ if $f(h(n)) < n + h(n)$, and $f_P(n) = n + h(n) - 1$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 2. -/
public theorem nthNonValue_eq_interleave_of_le_sub (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (α : ℕ → ℝ)
    (hα : ∀ m, 2 ≤ m → (f (m - 1) : ℝ) ≤ α m ∧ α m ≤ f m) (h : ℕ → ℕ)
    (hh : ∀ n, 1 ≤ n → 1 ≤ h n ∧ α (h n) ≤ n ∧ (n : ℝ) < α (h n + 1))
    (hfar : ∀ m : ℕ, 2 ≤ m → (m : ℝ) ≤ f m - α m) (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue f n = if f (h n) < n + h n then n + h n else n + h n - 1 := by
  obtain ⟨hhpos, _, hright⟩ := hh n hn
  have hnext := hfar (h n + 1) (by omega)
  have hlt : n + h n < f (h n + 1) := by
    have hlt' : (n : ℝ) + (h n : ℝ) < (f (h n + 1) : ℝ) := by
      rw [Nat.cast_add, Nat.cast_one] at hnext
      linarith
    exact_mod_cast hlt'
  rw [nthNonValue_eq_interleave f hf1 hgap α hα h hh n hn, ite_eq_right (Nat.not_le.mpr hlt)]
  by_cases hle : n + h n ≤ f (h n)
  · rw [ite_eq_left hle, ite_eq_right (not_lt_of_ge hle)]
  · rw [ite_eq_right hle, ite_eq_left (Nat.not_le.mp hle)]

end MetaMathlibExt
