/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.Enumerative.Catalan.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Whitt's generalized Catalan numbers

`whittGeneralizedCatalan α n = ∑_{k=0}^{n-1} (1 - k/n) C(n-1+k, k) α^k` (OEIS A064062 for
`α = 2`), from W. Whitt, *Fluid models for many-server queues with abandonments*, quoted as
`C(α, n+1) = ∑_{k=0}^{n} (1 - k/(n+1)) C(n+k, k) α^k` by Sabar Taoufik,
*A New Triangle of Numbers: Properties and Observations*, INTEGERS 26 (2026), Article A27,
Section 5.
-/

namespace MetaMathlibExt

@[expose] public section

/-- **Whitt's generalized Catalan numbers.** For a rational number $\alpha$ and a natural number
$n$, Whitt's generalized Catalan number $C(\alpha, n)$ is the rational number

$$C(\alpha, n) = \sum_{k=0}^{n-1} \left(1 - \frac{k}{n}\right) \binom{n-1+k}{k} \alpha^k.$$

In particular $C(\alpha, 0) = 0$, the empty sum. Writing $n + 1$ for $n$ gives the source's form
$C(\alpha, n+1) = \sum_{k=0}^{n} \left(1 - \frac{k}{n+1}\right) \binom{n+k}{k} \alpha^k$. For
$\alpha = 2$ and $n \ge 1$ these are the terms of OEIS A064062.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)`, quoting W. Whitt, J. Integer Seq. 14
(2011)). -/
def whittGeneralizedCatalan (α : ℚ) (n : ℕ) : ℚ :=
  ∑ k ∈ Finset.range n, (1 - (k : ℚ) / n) * ((n - 1 + k).choose k : ℚ) * α ^ k

/-- **Whitt's generalized Catalan numbers in the source's indexing.** For every rational number
$\alpha$ and every natural number $n$, Whitt's generalized Catalan number $C(\alpha, n + 1)$ is

$$C(\alpha, n + 1) = \sum_{k=0}^{n} \left(1 - \frac{k}{n+1}\right) \binom{n+k}{k} \alpha^k.$$

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)`). -/
theorem whittGeneralizedCatalan_succ (α : ℚ) (n : ℕ) :
    whittGeneralizedCatalan α (n + 1) =
      ∑ k ∈ Finset.range (n + 1),
        (1 - (k : ℚ) / ((n : ℚ) + 1)) * ((n + k).choose k : ℚ) * α ^ k := by
  simp [whittGeneralizedCatalan]

/-- **Whitt's generalized Catalan number at zero.** For every rational number $\alpha$, Whitt's
generalized Catalan number $C(\alpha, 0)$ equals $0$, being an empty sum.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)`). -/
@[simp] theorem whittGeneralizedCatalan_zero (α : ℚ) : whittGeneralizedCatalan α 0 = 0 := by
  simp [whittGeneralizedCatalan]

/-- **Whitt's generalized Catalan number at one.** For every rational number $\alpha$, Whitt's
generalized Catalan number $C(\alpha, 1)$ equals $1$.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)` at `n = 0`). -/
@[simp] theorem whittGeneralizedCatalan_one (α : ℚ) : whittGeneralizedCatalan α 1 = 1 := by
  simp [whittGeneralizedCatalan]

/-- **Whitt's generalized Catalan numbers with parameter zero.** For every natural number
$n \ge 1$, Whitt's generalized Catalan number $C(0, n)$ equals $1$: only the term $k = 0$ of the
defining sum survives.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (definition of `C(α, n+1)`). -/
theorem whittGeneralizedCatalan_zero_left {n : ℕ} (hn : 0 < n) :
    whittGeneralizedCatalan 0 n = 1 := by
  rw [whittGeneralizedCatalan, Finset.sum_eq_single 0]
  · simp
  · intro k _ hk
    simp [hk]
  · intro h
    exact absurd (Finset.mem_range.2 hn) h

/-- **First values of Whitt's generalized Catalan numbers with parameter two.** Whitt's
generalized Catalan numbers with parameter $\alpha = 2$ satisfy $C(2, 1) = 1$, $C(2, 2) = 3$,
$C(2, 3) = 13$ and $C(2, 4) = 67$.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Section 5 (OEIS A064062). -/
theorem whittGeneralizedCatalan_two_small :
    whittGeneralizedCatalan 2 1 = 1 ∧ whittGeneralizedCatalan 2 2 = 3 ∧
      whittGeneralizedCatalan 2 3 = 13 ∧ whittGeneralizedCatalan 2 4 = 67 := by
  simp [whittGeneralizedCatalan, Finset.sum_range_succ, Nat.choose]
  norm_num

-- The difference of adjacent binomial coefficients, with zero before the first entry.
private def whittChooseDiff (r k : ℕ) : ℚ :=
  2 * (r.choose k : ℚ) - (r + 1).choose k

private lemma whittChooseDiff_succ_succ (r k : ℕ) :
    whittChooseDiff (r + 1) (k + 1) = whittChooseDiff r (k + 1) + whittChooseDiff r k := by
  simp only [whittChooseDiff, Nat.choose_succ_succ', Nat.cast_add]
  ring

private lemma whittCoeff_eq_chooseDiff (n k : ℕ) :
    (1 - (k : ℚ) / ((n : ℚ) + 1)) * ((n + k).choose k : ℚ) = whittChooseDiff (n + k) k := by
  have h := Nat.choose_mul_succ_eq (n + k) k
  rw [Nat.add_right_comm n k 1, Nat.add_sub_cancel] at h
  have hq : ((n + k).choose k : ℚ) * ((n : ℚ) + 1 + k) =
      ((n + 1 + k).choose k : ℚ) * ((n : ℚ) + 1) := by exact_mod_cast h
  rw [whittChooseDiff, Nat.add_right_comm n k 1]
  field_simp
  linear_combination -hq

private lemma whittChooseDiff_diag (n : ℕ) : whittChooseDiff (n + n) n = catalan n := by
  have h : ((n : ℚ) + 1) * (catalan n : ℚ) = ((n + n).choose n : ℚ) := by
    exact_mod_cast (show (n + 1) * catalan n = (n + n).choose n by
      simpa only [Nat.centralBinom, two_mul] using succ_mul_catalan_eq_centralBinom n)
  rw [← whittCoeff_eq_chooseDiff, ← h]
  field_simp
  ring

/-- **Consecutive Whitt generalized Catalan numbers at $\alpha = 2$.** For every natural number
$n \ge 1$, Whitt's generalized Catalan numbers at $\alpha = 2$ satisfy

$$C(2, n) + C(2, n+1) = 2^{n+1} c_n,$$

where $c_n = \frac{1}{n+1}\binom{2n}{n}$ is the $n$-th Catalan number.

Source: Sabar Taoufik, *A New Triangle of Numbers: Properties and Observations*, INTEGERS 26
(2026), Article A27, Theorem 6 (`integers-2026-A27-thm-6`). -/
theorem whittGeneralizedCatalan_two_add_succ (n : ℕ) (hn : 1 ≤ n) :
    whittGeneralizedCatalan 2 n + whittGeneralizedCatalan 2 (n + 1) = 2 ^ (n + 1) * catalan n := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  let f (r k : ℕ) : ℚ := whittChooseDiff (r + k) k * 2 ^ k
  have hwhitt (r : ℕ) : whittGeneralizedCatalan 2 (r + 1) =
      ∑ k ∈ Finset.range (r + 1), f r k := by
    rw [whittGeneralizedCatalan_succ]
    simp only [f, whittCoeff_eq_chooseDiff]
  have hzero (r : ℕ) : f r 0 = 1 := by norm_num [f, whittChooseDiff]
  have hstep (k : ℕ) : f (n + 1) (k + 1) = f n (k + 1) + 2 * f (n + 1) k := by
    dsimp only [f]
    rw [Nat.add_right_comm n 1 (k + 1), whittChooseDiff_succ_succ, pow_succ,
      Nat.add_right_comm n 1 k, ← Nat.add_assoc n k 1]
    ring
  have hmid : f n (n + 1) = 0 := by
    dsimp only [f, whittChooseDiff]
    rw [show n + (n + 1) = 2 * n + 1 by omega,
      Nat.choose_succ_succ' (2 * n + 1) n, Nat.choose_symm_half, Nat.cast_add]
    ring
  -- Summing Pascal's identity shifts the second sum by one power of two.
  have hsum : (∑ k ∈ Finset.range (n + 1 + 1), f (n + 1) k) =
      (∑ k ∈ Finset.range (n + 1 + 1), f n k) + 2 * ∑ k ∈ Finset.range (n + 1), f (n + 1) k := by
    rw [Finset.sum_range_succ' (f (n + 1)) (n + 1), Finset.sum_range_succ' (f n) (n + 1)]
    simp only [hstep, hzero, Finset.sum_add_distrib, ← Finset.mul_sum]
    ring
  rw [Finset.sum_range_succ (f n), hmid, add_zero, ← hwhitt n, ← hwhitt (n + 1)] at hsum
  have hlast := hwhitt (n + 1)
  rw [Finset.sum_range_succ, show f (n + 1) (n + 1) = (catalan (n + 1) : ℚ) * 2 ^ (n + 1) by
    simp only [f, whittChooseDiff_diag]] at hlast
  rw [pow_succ]
  linear_combination 2 * hlast - hsum

end

end MetaMathlibExt
