/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.FixedPointsKPermutations
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The fixed-point distribution at a given cycle count

The fixed-point count is bounded by the cycle count, and the empty permutation contributes once.
Marking one fixed point reduces the second moment to the first moment on one fewer element,
giving Benoumhani's variance formula.
-/

namespace MetaMathlibExt

open Finset

/-- **A permutation has at most as many fixed points as cycles.** Write $a(n, k, j)$ for the number
of permutations of an $n$-element set with exactly $k$ cycles (fixed points counted as cycles of
length one) and exactly $j$ fixed points. If $k < j$, then $a(n, k, j) = 0$.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (range `0 ≤ j ≤ k` of `a(n, k, j)`). -/
public theorem kPermFixedPointCount_eq_zero_of_lt {n k j : ℕ} (h : k < j) :
    kPermFixedPointCount n k j = 0 := by
  unfold kPermFixedPointCount
  rw [Fintype.card_eq_zero_iff]
  exact ⟨fun ⟨σ, h1, h2⟩ => by rw [cycleQuotientCount_eq] at h1; omega⟩

/-- **Counting the empty permutation.** Write $a(n, k, j)$ for the number of permutations of an
$n$-element set with exactly $k$ cycles (fixed points counted as cycles of length one) and exactly
$j$ fixed points. Then $a(0, 0, 0) = 1$: the empty permutation is the only permutation of the
empty set, and it has no cycles and no fixed points.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 3 (definition of `a(n, k, j)`, value at
`n = k = j = 0`). -/
public theorem kPermFixedPointCount_zero_zero_zero : kPermFixedPointCount 0 0 0 = 1 := by
  unfold kPermFixedPointCount
  rw [Fintype.card_eq_one_iff]
  refine ⟨⟨1, by rw [cycleQuotientCount_eq]; simp, by simp⟩,
    fun x => Subtype.ext (Subsingleton.elim _ _)⟩

private theorem total_count (n k : ℕ) :
    ∑ j ∈ range (k + 1), kPermFixedPointCount n k j = Nat.stirlingFirst n k := by
  classical
  rw [← card_perm_cycleCount_eq_stirlingFirst]
  simp only [kPermFixedPointCount, cycleQuotientCount_eq, Fintype.card_subtype]
  symm
  simp_rw [← filter_filter]
  apply card_eq_sum_card_fiberwise
  intro σ hσ
  have h := (mem_filter.mp hσ).2
  exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_add_left _ _).trans_eq h))

-- Weight a permutation by a function of its fixed-point count, then mark one fixed point.
private theorem sum_marked (n k : ℕ) (w : ℕ → ℕ) :
    ∑ j ∈ range (k + 2), w j * j * kPermFixedPointCount (n + 1) (k + 1) j =
      (n + 1) * ∑ j ∈ range (k + 1), w (j + 1) * kPermFixedPointCount n k j := by
  rw [sum_range_succ', mul_sum]
  simp only [mul_zero, zero_mul, add_zero]
  apply sum_congr rfl
  intro j hj
  have hjk : j ≤ k := Nat.le_of_lt_succ (mem_range.mp hj)
  rw [kPermFixedPointCount_eq_choose_mul_derangement (Nat.succ_le_succ hjk),
    kPermFixedPointCount_eq_choose_mul_derangement (n := n) hjk]
  simp only [Nat.succ_sub_succ_eq_sub]
  simpa only [mul_comm, mul_left_comm, mul_assoc] using
    congrArg (fun t => w (j + 1) * t * kPermFixedPointCount (n - j) (k - j) 0)
      (Nat.add_one_mul_choose_eq n j).symm

private theorem second_moment (n k : ℕ) :
    ∑ j ∈ range (k + 3), j ^ 2 * kPermFixedPointCount (n + 2) (k + 2) j =
      (n + 2) * ((n + 1) * Nat.stirlingFirst n k + Nat.stirlingFirst (n + 1) (k + 1)) := by
  have hfirst := sum_marked n k (fun _ => 1)
  simp only [one_mul, total_count] at hfirst
  simpa only [Nat.add_assoc, Nat.reduceAdd, add_mul, one_mul, sum_add_distrib, hfirst, total_count,
    pow_two] using sum_marked (n + 1) (k + 1) (fun j => j)

private theorem stirling_pos (n k : ℕ) (h : k ≤ n) :
    0 < Nat.stirlingFirst (n + 1) (k + 1) := by
  induction n, h using Nat.le_induction with
  | base => simp [Nat.stirlingFirst_self]
  | succ n _ ih =>
    rw [Nat.stirlingFirst_succ_succ]
    exact Nat.add_pos_left (Nat.mul_pos (Nat.succ_pos _) ih) _

/-- **Variance of the number of fixed points of a permutation with a given number of cycles.**
Write $a(n, k, j)$ for the number of permutations of an $n$-element set with exactly $k$ cycles
(fixed points counted as cycles of length one) and exactly $j$ fixed points, $c(n, k)$ for the
unsigned Stirling number of the first kind (the number of permutations of an $n$-element set
with $k$ cycles), and $\mu_{n,k} = n \, c(n - 1, k - 1) / c(n, k)$. If $2 \le k \le n$, then
$\frac{1}{c(n, k)} \sum_{j=0}^{k} j^2 \, a(n, k, j) - \mu_{n,k}^2 =
\mu_{n,k} (1 + \mu_{n-1,k-1} - \mu_{n,k})$.

Here $\mu_{n,k}$ is the mean number of fixed points of a uniformly random permutation of an
$n$-element set with $k$ cycles, so the left side is the variance of that number.

Source: Moussa Benoumhani, *The Distribution of the Number of Fixed Points in k-Permutations*,
INTEGERS 24 (2024), Article A54, Proposition 4 (`integers-2024-A54-prop-4`). -/
public theorem kPermFixedPoint_variance {n k : ℕ} (hk : 2 ≤ k) (hkn : k ≤ n) :
    let μ : ℕ → ℕ → ℚ := fun n k =>
      (n : ℚ) * Nat.stirlingFirst (n - 1) (k - 1) / Nat.stirlingFirst n k
    (∑ j ∈ Finset.range (k + 1), (j : ℚ) ^ 2 * kPermFixedPointCount n k j) /
        Nat.stirlingFirst n k - μ n k ^ 2 =
      μ n k * (1 + μ (n - 1) (k - 1) - μ n k) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le' hk
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le' (show 2 ≤ n by omega)
  dsimp only
  have hsum : (∑ j ∈ range (k + 3), (j : ℚ) ^ 2 * kPermFixedPointCount (n + 2) (k + 2) j) =
      (n + 2 : ℚ) * ((n + 1) * Nat.stirlingFirst n k + Nat.stirlingFirst (n + 1) (k + 1)) := by
    exact_mod_cast second_moment n k
  rw [hsum]
  have h₁ : (Nat.stirlingFirst (n + 1) (k + 1) : ℚ) ≠ 0 := by
    exact_mod_cast (stirling_pos n k (by omega)).ne'
  have h₂ : (Nat.stirlingFirst (n + 2) (k + 2) : ℚ) ≠ 0 := by
    exact_mod_cast (stirling_pos (n + 1) (k + 1) (by omega)).ne'
  simp only [Nat.reduceSubDiff, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  field_simp
  ring

end MetaMathlibExt
