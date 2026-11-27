/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.ComplementarySequences

/-!
# Complementary sequences with a close interleaving function

When the interleaving function stays close to the sequence, the general three-case formula
reduces to two cases.

## References

* Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025), Article A95,
  Theorem 3 and Corollary 1 (p. 7).
* J. Lambek and L. Moser, *Inverse and Complementary Sequences of Natural Numbers*, American
  Mathematical Monthly 61 (1954), no. 7, pp. 454–458, for the complementary-sequence method
  discussed by Wu in §2.1.
-/

namespace MetaMathlibExt

/-- **Interleaving formula when $f(m) - \alpha(m) < m$.** Let
$f : \mathbb{N} \to \mathbb{N}$ satisfy $f(1) \ge 1$ and $f(m + 1) \ge f(m) + m$ for all $m \ge 1$,
and for $n \ge 1$ let $f_P(n)$ be the $n$-th positive integer that is not a value $f(m)$ with
$m \ge 1$. Let $\alpha : \mathbb{N} \to \mathbb{R}$ satisfy $f(m - 1) \le \alpha(m) \le f(m)$ for
all $m \ge 2$, and let $h : \mathbb{N} \to \mathbb{N}$ satisfy $h(n) \ge 1$ and
$\alpha(h(n)) \le n < \alpha(h(n) + 1)$ for all $n \ge 1$.
Suppose moreover that $f(m) - \alpha(m) < m$ for all $m \ge 1$. Then for every $n \ge 1$,
$f_P(n) = n + h(n) + 1$ if $f(h(n) + 1) \le n + h(n)$, and $f_P(n) = n + h(n)$ otherwise.

Source: Chai Wah Wu, *Algorithms for Complementary Sequences*, INTEGERS 25 (2025),
Article A95, Corollary 1. -/
public theorem nthNonValue_eq_interleave_of_sub_lt (f : ℕ → ℕ) (hf1 : 1 ≤ f 1)
    (hgap : ∀ m, 1 ≤ m → f m + m ≤ f (m + 1)) (α : ℕ → ℝ)
    (hα : ∀ m, 2 ≤ m → (f (m - 1) : ℝ) ≤ α m ∧ α m ≤ f m) (h : ℕ → ℕ)
    (hh : ∀ n, 1 ≤ n → 1 ≤ h n ∧ α (h n) ≤ n ∧ (n : ℝ) < α (h n + 1))
    (hclose : ∀ m : ℕ, 1 ≤ m → (f m : ℝ) - α m < m) (n : ℕ) (hn : 1 ≤ n) :
    nthNonValue f n = if f (h n + 1) ≤ n + h n then n + h n + 1 else n + h n := by
  obtain ⟨hpos, hle, _⟩ := hh n hn
  have hltReal : (f (h n) : ℝ) < (n : ℝ) + h n := by
    rw [add_comm]
    exact (sub_lt_iff_lt_add.mp (hclose (h n) hpos)).trans_le (add_le_add le_rfl hle)
  have hlt : f (h n) < n + h n := by exact_mod_cast hltReal
  rw [nthNonValue_eq_interleave f hf1 hgap α hα h hh n hn, ite_eq_right (not_le_of_gt hlt)]

end MetaMathlibExt
