/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Field.Rat
public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Tactic.Ring

/-!
# The Zerroukhat–Khaldi sums

The recurrence for the sum $U$ follows by applying the Stirling recurrence to its defining sum
and shifting the summation index.
-/

@[expose] public section

namespace MathlibExt.NumberTheory.GenocchiExplicitWanted

/-- **The Zerroukhat–Khaldi sum $U(m, k)$.** For natural numbers $m$ and $k$, define the rational
number
$$U(m, k) = \sum_{j=0}^{m} (-1)^{k+j+m} \frac{(k+j-1)!}{2^{k+j-1}} S(m, j),$$
where $S(m, j)$ is the Stirling number of the second kind and, in the term with $k = j = 0$,
$k + j - 1$ is read as $0$, so that this term is $(-1)^m S(m, 0)$. -/
def zerroU (m k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (m + 1),
    (-1 : ℚ) ^ (k + j + m) * ((k + j - 1).factorial : ℚ) /
      2 ^ (k + j - 1) * (Nat.stirlingSecond m j : ℚ)

private theorem sum_stirlingSecond_succ (r : ℕ) (f : ℕ → ℚ) :
    ∑ j ∈ Finset.range (r + 1 + 1), f j * Nat.stirlingSecond (r + 1) j =
      ∑ j ∈ Finset.range (r + 1), (f j * j + f (j + 1)) * Nat.stirlingSecond r j := by
  -- The shifted sum agrees with the unshifted one because both boundary terms vanish.
  have shift :
      ∑ j ∈ Finset.range (r + 1), f (j + 1) * (j + 1 : ℕ) * Nat.stirlingSecond r (j + 1) =
        ∑ j ∈ Finset.range (r + 1), f j * j * Nat.stirlingSecond r j := by
    rw [Finset.sum_range_succ _ r,
      Finset.sum_range_succ' (fun j ↦ f j * j * Nat.stirlingSecond r j)]
    simp [Nat.stirlingSecond_eq_zero_of_lt r.lt_succ_self]
  rw [Finset.sum_range_succ' _ (r + 1)]
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero,
    Nat.stirlingSecond_succ_succ, Nat.cast_add _ (Nat.stirlingSecond r _), Nat.cast_mul]
  simp only [mul_add, add_mul, ← mul_assoc, Finset.sum_add_distrib, shift]

/-- **Recurrence for the Zerroukhat–Khaldi sums $U$.** Let $U(m, k)$ be the Zerroukhat–Khaldi
sum. For all natural numbers $r$ and $k$ with $k \ge 1$,
$U(r+1, k) = U(r, k+1) + k \, U(r, k)$.

Source: Schehrazade Zerroukhat and Laala Khaldi, "A Note
on Explicit Formulas for Bernoulli and Genocchi Numbers",
Lemma 3. -/
theorem zerroU_succ (r k : ℕ) (hk : 1 ≤ k) :
    zerroU (r + 1) k = zerroU r (k + 1) + (k : ℚ) * zerroU r k := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  unfold zerroU
  rw [sum_stirlingSecond_succ, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  -- Expand the next factorial and the next powers of −1 and 2 in the coefficient of S(r,j).
  simp only [Nat.succ_add, Nat.add_succ, Nat.succ_sub_one,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ, Nat.cast_add, pow_succ, div_eq_mul_inv,
    mul_inv_rev]
  ring

end MathlibExt.NumberTheory.GenocchiExplicitWanted
