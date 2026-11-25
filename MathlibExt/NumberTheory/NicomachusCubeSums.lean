/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Cube sums in the generalized Nicomachus identity

Kim and Stolarsky express the difference between a cube sum and a square in terms of a
polynomial. This module defines the sums, squares and polynomials for both parities and proves
the even case, `nicomachusLEven_sub_REven_eq`.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.NicomachusGeneralizationWanted

/-- **Triangular numbers as reals.** For a natural number $m$, $T_m = m(m+1)/2$ is the $m$-th
triangular number, viewed as a real number. -/
noncomputable def nicomachusTriangular (m : ℕ) : ℝ := (m : ℝ) * ((m : ℝ) + 1) / 2

/-- **The odd-case cube sum $L_{m,o}$.** For a natural number $m$ and a real number $x$,
$$L_{m,o}(x) = \sum_{j=1}^{m} (2j - 1)^3 + x^3 +
\sum_{j=2}^{m} \bigl((2j - 2) + (j - 1)x\bigr)^3.$$ -/
def nicomachusLOdd (m : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) - 1) ^ 3) + x ^ 3 +
    ∑ j ∈ Finset.Icc 2 m, ((2 * (j : ℝ) - 2) + ((j : ℝ) - 1) * x) ^ 3

/-- **The odd-case square $R_{m,o}(x)$.** For a natural number $m$ and a real number $x$,
$$R_{m,o}(x) = \bigl(T_{2m-1} + (1 + T_{m-1})\,x\bigr)^2,$$
where $T_n = n(n+1)/2$ is the $n$-th triangular number (for $m = 0$ the indices $2m - 1$ and
$m - 1$ are read as $0$). -/
noncomputable def nicomachusROdd (m : ℕ) (x : ℝ) : ℝ :=
  (nicomachusTriangular (2 * m - 1) +
    (1 + nicomachusTriangular (m - 1)) * x) ^ 2

/-- **The odd-case polynomial $P_{m,o}$.** For a natural number $m$ and a real number $x$,
$$P_{m,o}(x) = \sum_{j=0}^{m} (4j + 1 + jx) \bigl((j + 1)(j - 2) + j^2 x\bigr).$$ -/
def nicomachusPOdd (m : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.Icc 0 m,
    (4 * (j : ℝ) + 1 + (j : ℝ) * x) *
      (((j : ℝ) + 1) * ((j : ℝ) - 2) + (j : ℝ) ^ 2 * x)

/-- **The even-case cube sum $L_{m,e}$.** For a natural number $m$ and a real number $x$,
$$L_{m,e}(x) = \sum_{j=1}^{m} (2j - 1)^3 + x^3 + \sum_{j=1}^{m} (2j + jx)^3.$$ -/
def nicomachusLEven (m : ℕ) (x : ℝ) : ℝ :=
  (∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) - 1) ^ 3) + x ^ 3 +
    ∑ j ∈ Finset.Icc 1 m, (2 * (j : ℝ) + (j : ℝ) * x) ^ 3

/-- **The even-case square $R_{m,e}$.** For a natural number $m$ and a real number $x$,
$$R_{m,e}(x) = \bigl(T_{2m} + (1 + T_m)\,x\bigr)^2,$$
where $T_n = n(n+1)/2$ is the $n$-th triangular number. -/
noncomputable def nicomachusREven (m : ℕ) (x : ℝ) : ℝ :=
  (nicomachusTriangular (2 * m) +
    (1 + nicomachusTriangular m) * x) ^ 2

/-- **Faulhaber expansion of the odd-case polynomial.** For real numbers $m$ and $x$, let
$$\widetilde{P}(m, x) = -2(m + 1) - (9 + 2x) \, \frac{m(m+1)}{2} - 3 \cdot \frac{m(m+1)(2m+1)}{6} +
(4 + 5x + x^2) \left(\frac{m(m+1)}{2}\right)^2.$$

This is the polynomial in $m$ obtained from the sum defining the odd-case polynomial
$P_{m,o}(x)$ by the Faulhaber formulas for $\sum_{j=0}^{m} j^p$ with $p \le 3$; it agrees with
$P_{m,o}(x)$ at every natural number $m$. -/
noncomputable def nicomachusPClosed (m x : ℝ) : ℝ :=
  (-2) * (m + 1) + (-9 - 2 * x) * (m * (m + 1) / 2) +
    (-3) * (m * (m + 1) * (2 * m + 1) / 6) +
      (4 + 5 * x + x ^ 2) * (m * (m + 1) / 2) ^ 2

/-- **The even-case polynomial $P_{m,e}$.** For a natural number $m$ and a real number $x$,
$P_{m,e}(x) = \widetilde{P}(-m - 1, x)$, where $\widetilde{P}(m, x)$ is the Faulhaber expansion
of the odd-case polynomial $P_{m,o}(x)$ as a polynomial in $m$ (the paper defines $P_{m,e}(x)$
by substituting $-m - 1$ for $m$ in that expansion). -/
noncomputable def nicomachusPEven (m : ℕ) (x : ℝ) : ℝ :=
  nicomachusPClosed (-(m : ℝ) - 1) x

/-- **Generalized Nicomachus identity, even case.** Let $L_{m,e}$ be the even-case cube sum,
$R_{m,e}$ the even-case square and $P_{m,e}$ the even-case polynomial. For every natural number
$m \ge 2$ and every real number $x$,
$$L_{m,e}(x) - R_{m,e}(x) = x \, P_{m,e}(x) - x^2 + x^3.$$

Source: Seon-Hong Kim and Kenneth B. Stolarsky, "A Balanced
Three or More-term Generalization of Nicomachus' Identity", Theorem 1. -/
theorem nicomachusLEven_sub_REven_eq (m : ℕ) (hm : 2 ≤ m)
    (x : ℝ) :
    nicomachusLEven m x - nicomachusREven m x =
      x * nicomachusPEven m x - x ^ 2 + x ^ 3 := by
  unfold nicomachusLEven nicomachusREven nicomachusTriangular nicomachusPEven nicomachusPClosed
  induction m, hm using Nat.le_induction with
  | base =>
    norm_num [show Finset.Icc 1 2 = {1, 2} by decide, Finset.sum_insert]
    ring
  | succ m _ ih =>
    -- The two sums gain their final cubes. The remaining difference is a polynomial identity.
    simp only [Finset.sum_Icc_succ_top (Nat.succ_le_succ (Nat.zero_le m))]
    push_cast at ih ⊢
    linear_combination ih

end MathlibExt.NumberTheory.NicomachusGeneralizationWanted
