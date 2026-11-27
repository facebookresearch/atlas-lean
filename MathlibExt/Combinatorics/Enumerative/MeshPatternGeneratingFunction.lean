/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Ring.RingNF

@[expose] public section

namespace MetaMathlibExt

/--
**Product formula from the mesh-pattern recurrence.** Let $R$ be a commutative semiring, let
$x \in R$, let $0 < k \le n$ be natural numbers, and let $P(m, r) \in R$ for natural numbers
$m, r$. Natural numbers are mapped into $R$. Suppose that $P(k-1, k) = (k-1)!$ and that
$P(m, k) = (x + (m - 1))\,P(m-1, k)$ for every natural number $m \ge k$. Then

$$P(n, k) = (k-1)! \prod_{i=0}^{n-k} \bigl(x + (k - 1 + i)\bigr).$$

With $R$ the polynomials over $\mathbb{N}$ and $x$ the variable, this is the product formula for
the mesh-pattern counting polynomial.

Source: Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling
Numbers," Journal of Integer Sequences 18 (2015), Article 15.10.1,
Corollary (label cor:genfunc), line 194, with the recurrence and base value
from Theorem (label thm:main), line 175,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.
-/
theorem meshPatternGeneratingFunction_eq_factorial_mul_prod_general {R : Type*} [CommSemiring R]
    (P : ℕ → ℕ → R) (n k : ℕ) (x : R)
    (hk : 0 < k) (hnk : k ≤ n)
    (hbase : P (k - 1) k = (Nat.factorial (k - 1) : R))
    (hstep : ∀ m : ℕ, k ≤ m →
      P m k = (x + ((m - 1 : ℕ) : R)) * P (m - 1) k) :
    P n k =
      (Nat.factorial (k - 1) : R) *
        ∏ i ∈ Finset.range (n - k + 1),
          (x + ((k - 1 + i : ℕ) : R)) := by
  induction n, hnk using Nat.le_induction with
  | base =>
    have h1 := hstep k (by omega : k ≤ k)
    rw [hbase] at h1
    rw [h1]
    have hkk : k - k + 1 = 1 := by omega
    rw [hkk, Finset.prod_range_succ]
    simp
    ring
  | succ n hkn ih =>
    have hstep' := hstep (n + 1) (by omega : k ≤ n + 1)
    have hn1 : n + 1 - 1 = n := by omega
    rw [hn1] at hstep'
    rw [hstep', ih]
    have hrange : n + 1 - k + 1 = (n - k + 1) + 1 := by omega
    have hcast : (k - 1 + (n - k + 1) : ℕ) = n := by omega
    have hprod : (∏ i ∈ Finset.range (n + 1 - k + 1),
        (x + ((k - 1 + i : ℕ) : R))) =
        (∏ i ∈ Finset.range (n - k + 1),
          (x + ((k - 1 + i : ℕ) : R))) *
        (x + (((k - 1 + (n - k + 1) : ℕ)) : R)) := by
      rw [hrange, Finset.prod_range_succ]
    rw [hprod, hcast]
    ring

/--
**Product formula from the mesh-pattern recurrence, real case.** Let $0 < k \le n$ be natural
numbers, let $x$ be a real number, and let $P(m, r, y)$ be real numbers indexed by natural
numbers $m, r$ and a real number $y$. Suppose that $P(k-1, k, x) = (k-1)!$ and that
$P(m, k, x) = (x + m - 1)\,P(m-1, k, x)$ for every natural number $m \ge k$. Then

$$P(n, k, x) = (k-1)! \prod_{i=0}^{n-k} (x + k - 1 + i).$$

Source: Matt Davis, "Quadrant Marked Mesh Patterns and the r-Stirling
Numbers," Journal of Integer Sequences 18 (2015), Article 15.10.1,
Corollary (label cor:genfunc), line 194, with the recurrence and base value
from Theorem (label thm:main), line 175,
<https://cs.uwaterloo.ca/journals/JIS/VOL18/Davis/davis3.tex>.
Proves `Wanted` entry `meshPatternGeneratingFunction_eq_factorial_mul_prod`.
-/
theorem meshPatternGeneratingFunction_eq_factorial_mul_prod
    (P : ℕ → ℕ → ℝ → ℝ) (n k : ℕ) (x : ℝ)
    (hk : 0 < k) (hnk : k ≤ n)
    (hbase : P (k - 1) k x = (Nat.factorial (k - 1) : ℝ))
    (hstep : ∀ m : ℕ, k ≤ m →
      P m k x = (x + ((m - 1 : ℕ) : ℝ)) * P (m - 1) k x) :
    P n k x =
      (Nat.factorial (k - 1) : ℝ) *
        ∏ i ∈ Finset.range (n - k + 1),
          (x + ((k - 1 + i : ℕ) : ℝ)) := by
  exact meshPatternGeneratingFunction_eq_factorial_mul_prod_general (fun m r => P m r x) n k x
    hk hnk hbase hstep

end MetaMathlibExt
