/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Mathlib.Combinatorics.Enumerative.Stirling
public import Mathlib.NumberTheory.Bernoulli
import MathlibExt.NumberTheory.Bernoulli.KanekoBernoulliStirling

/-!
# Weighted alternating sums of Stirling numbers

Farhi's identity expresses a weighted sum of Stirling numbers of the second kind
as a linear combination of consecutive Bernoulli numbers.
-/

namespace MathlibExt.NumberTheory.BernoulliSecondKindWanted

open Finset

private def weight (r k : ℕ) : ℚ :=
  (-1 : ℚ) ^ k * ((k.factorial : ℚ) / (k + r))

private def weightedSum (r n : ℕ) : ℚ :=
  ∑ k ∈ range (n + 1), weight r k * Nat.stirlingSecond n k

private noncomputable def bernoulliSum (r n : ℕ) : ℚ :=
  ∑ k ∈ range r, (Nat.stirlingFirst r (k + 1) : ℚ) * bernoulli (n + k)

private theorem weightedSum_one (n : ℕ) : weightedSum 1 n = bernoulli n := by
  rw [MetaMathlibExt.kaneko_bernoulli_stirling_sum, ← Ico_add_one_right_eq_Icc,
    sum_Ico_eq_sum_range]
  simp only [Nat.add_sub_cancel, Nat.add_comm 1, Nat.cast_add,
    Nat.cast_one, weightedSum, weight]
  exact sum_congr rfl fun k _ => by ring

-- The second-kind recurrence acts on the weights by f(k) ↦ k f(k) + f(k+1).
private theorem sum_stirlingSecond_succ (f : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ range (n + 2), f k * Nat.stirlingSecond (n + 1) k =
      ∑ k ∈ range (n + 1), (f k * k + f (k + 1)) * Nat.stirlingSecond n k := by
  let g (k : ℕ) := f k * k * Nat.stirlingSecond n k
  have shift := (sum_range_succ' g (n + 1)).symm.trans (sum_range_succ g (n + 1))
  have hg : ∑ k ∈ range (n + 1), g (k + 1) = ∑ k ∈ range (n + 1), g k := by
    simpa [g, Nat.stirlingSecond_eq_zero_of_lt n.lt_succ_self] using shift
  rw [sum_range_succ' _ (n + 1)]
  simp only [Nat.stirlingSecond_succ_zero, Nat.cast_zero, mul_zero, add_zero,
    Nat.stirlingSecond_succ_succ, Nat.cast_add (_ * _) _, Nat.cast_mul]
  simp only [mul_add, ← mul_assoc, add_mul, sum_add_distrib]
  exact congrArg (· + _) hg

private theorem weightedSum_step (r n : ℕ) (hr : 0 < r) :
    (r : ℚ) * weightedSum (r + 1) n = r * weightedSum r n + weightedSum r (n + 1) := by
  unfold weightedSum
  rw [sum_stirlingSecond_succ, mul_sum, mul_sum, ← sum_add_distrib]
  refine sum_congr rfl fun k _ => ?_
  have hr' : (0 : ℚ) < r := by exact_mod_cast hr
  simp only [weight, pow_succ, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
  field_simp
  ring

private theorem bernoulliSum_step (r n : ℕ) (hr : 0 < r) :
    bernoulliSum (r + 1) n = r * bernoulliSum r n + bernoulliSum r (n + 1) := by
  unfold bernoulliSum
  simp only [Nat.stirlingFirst_succ_succ, Nat.cast_add, Nat.cast_mul, add_mul,
    sum_add_distrib, mul_assoc, ← mul_sum]
  congr 1
  · rw [sum_range_succ]
    simp [Nat.stirlingFirst_eq_zero_of_lt r.lt_succ_self]
  · rw [sum_range_succ']
    obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr.ne'
    simp only [Nat.stirlingFirst_succ_zero, Nat.cast_zero, zero_mul, add_zero]
    exact sum_congr rfl fun k _ => by rw [show n + (k + 1) = n + 1 + k by omega]

/-- **Weighted alternating sums of Stirling numbers of the second kind.** For natural numbers
$r \ge 1$ and $n$, write $S(n,k)$ for the Stirling numbers of the second kind, $c(r,j)$ for the
unsigned Stirling numbers of the first kind, and $B_m$ for the Bernoulli numbers with
$B_1 = -\tfrac12$. Then, in $\mathbb{Q}$,
$$
\sum_{k=0}^{n} (-1)^k \frac{k!}{k+r} S(n,k) = \frac{1}{(r-1)!} \sum_{k=0}^{r-1} c(r,k+1) B_{n+k}.
$$

Source: Bakir Farhi, "Formulas Involving Bernoulli and
Stirling Numbers of Both Kinds", Theorem 17. -/
public theorem sum_stirlingSecond_div_add (r n : ℕ)
    (hr : 1 ≤ r) :
    ∑ k ∈ Finset.range (n + 1), (-1 : ℚ) ^ k *
        ((k.factorial : ℚ) / (k + r)) *
        (Nat.stirlingSecond n k : ℚ) =
      (1 / ((r - 1).factorial : ℚ)) *
        ∑ k ∈ Finset.range r,
          (Nat.stirlingFirst r (k + 1) : ℚ) * bernoulli (n + k) := by
  obtain ⟨s, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  clear hr
  change weightedSum (s + 1) n = 1 / (s.factorial : ℚ) * bernoulliSum (s + 1) n
  rw [one_div_mul_eq_div, eq_div_iff (by positivity)]
  induction s generalizing n with
  | zero => simp [weightedSum_one, bernoulliSum, Nat.stirlingFirst_self]
  | succ s ih =>
    rw [bernoulliSum_step (s + 1) n (by omega), ← ih n, ← ih (n + 1), Nat.factorial_succ]
    have h := weightedSum_step (s + 1) n (by omega)
    push_cast at h ⊢
    linear_combination (s.factorial : ℚ) * h

end MathlibExt.NumberTheory.BernoulliSecondKindWanted
