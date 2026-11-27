/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.NumberTheory.Recurrences.SuperLeonardoPBinomial
import Mathlib.Algebra.BigOperators.Ring.Finset
import Lean.Elab.Tactic.Omega

/-! # Supergeneralized Leonardo p-numbers via Fibonacci p-numbers -/

namespace MetaMathlibExt

/-- **Supergeneralized Leonardo p-numbers via Fibonacci p-numbers.** For all natural numbers
$p \ge 1$, $k$ and $n$ with $n > p$ and every real sequence $x$, the supergeneralized Leonardo
$p$-numbers $\mathcal{L}_{p,k,x}$ and the Fibonacci $p$-numbers $F_p$ satisfy
$$\mathcal{L}_{p,k,x}(n) = F_p(n-p+1)\,x_p + \sum_{i=0}^{\min(p-1,\,n-p-1)} F_p(n-p-i)\,x_i +
\max\Big\{0, \sum_{j=0}^{\lfloor (n-p)/(p+1) \rfloor} \binom{n-p-pj}{j+1}\Big\} \cdot k.$$

This is Corollary 7 of the paper with the factor $k$ restored. The printed corollary omits the
factor $k$ on the last term (and reuses $k$ as the summation index); without it the identity
fails, e.g. at $p = 1$, $k = 2$, $n = 2$, $x = (1, 1)$: $\mathcal{L}_{p,k,x}(n) = 4$ but the
printed right side is $3$. The factor is the one in Theorem 3, of which the corollary is stated
to be an immediate combination with Theorems 4 and 5.

Source: Clemens Schütz and Kristian Kelly, *An Explicit Formula for Supergeneralized
Leonardo `p`-numbers*, Journal of Integer Sequences 28 (2025), Article 25.8.2,
Corollary 7. -/
public theorem superLeonardoP_eq_fibonacciP_sum (p k : ℕ) (hp : 1 ≤ p) (x : ℕ → ℝ) (n : ℕ)
    (hn : p < n) :
    superLeonardoP p k x n =
      (fibonacciP p (n - p + 1) : ℝ) * x p +
        (∑ i ∈ Finset.range (min (p - 1) (n - p - 1) + 1),
          (fibonacciP p (n - p - i) : ℝ) * x i) +
        max 0 (∑ j ∈ Finset.range ((n - p) / (p + 1) + 1),
          ((n - p - p * j).choose (j + 1) : ℝ)) * k := by
  have weight (t : ℕ) : (fibonacciP p (t + 1) : ℝ) =
      ∑ j ∈ Finset.range (t / (p + 1) + 1), ((t - j * p).choose j : ℝ) := by
    rw [fibonacciP_succ_eq_sum_choose p t hp, Nat.cast_sum]
  rw [superLeonardoP_eq_sum_choose p k hp x n hn, ← weight (n - p)]
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  have hi' := Finset.mem_range.mp hi
  have h : 1 ≤ n - p - i := by omega
  congr 1
  simpa only [Nat.sub_add_cancel h] using (weight (n - p - i - 1)).symm

end MetaMathlibExt
