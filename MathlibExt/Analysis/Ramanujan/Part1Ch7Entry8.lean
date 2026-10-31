/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Data.Complex.Basic
public import Mathlib.NumberTheory.BernoulliPolynomials

@[expose] public section

/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 8

Bernoulli-polynomial difference over r+1 equals a Bernoulli-number sum.
-/

namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry8

open scoped Nat Real BigOperators Interval Polynomial
open Filter Finset Complex Topology

noncomputable section

/-- Shift identity for the complex Bernoulli polynomial, from
`Polynomial.bernoulli_comp_one_add_X`. -/
private theorem eval₂_bernoulli_shift (n : ℕ) (x : ℂ) :
    (Polynomial.bernoulli n).eval₂ (algebraMap ℚ ℂ) (x + 1) =
      (Polynomial.bernoulli n).eval₂ (algebraMap ℚ ℂ) x + (n : ℂ) * x ^ (n - 1) := by
  have h := Polynomial.bernoulli_comp_one_add_X n
  have hC := congrArg (Polynomial.map (algebraMap ℚ ℂ)) h
  rw [Polynomial.map_comp] at hC
  have hmap1 : Polynomial.map (algebraMap ℚ ℂ) (1 + Polynomial.X : Polynomial ℚ)
      = (1 + Polynomial.X : Polynomial ℂ) := by simp
  rw [hmap1] at hC
  have hmapR : Polynomial.map (algebraMap ℚ ℂ)
      (Polynomial.bernoulli n + n • Polynomial.X ^ (n - 1) : Polynomial ℚ)
      = Polynomial.map (algebraMap ℚ ℂ) (Polynomial.bernoulli n) +
        n • (Polynomial.X : Polynomial ℂ) ^ (n - 1) := by simp [Polynomial.map_add]
  rw [hmapR] at hC
  have hE := congrArg (Polynomial.eval x) hC
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_one] at hE
  have hE2 : Polynomial.eval x (n • (Polynomial.X : Polynomial ℂ) ^ (n - 1))
      = (n : ℂ) * x ^ (n - 1) := by
    rw [nsmul_eq_mul]
    simp [Polynomial.eval_mul, Polynomial.eval_pow]
  rw [hE2] at hE
  simp only [Polynomial.eval_map] at hE
  rw [show x + 1 = 1 + x from add_comm x 1]
  exact hE

/-- Explicit coefficient expansion of the complex Bernoulli polynomial, from
`Polynomial.coeff_bernoulli`. -/
private theorem eval₂_bernoulli_expand (n : ℕ) (x : ℂ) :
    (Polynomial.bernoulli n).eval₂ (algebraMap ℚ ℂ) x =
      ∑ k ∈ Finset.range (n + 1),
        ((n.choose k : ℕ) : ℂ) * ((bernoulli k : ℚ) : ℂ) * x ^ (n - k) := by
  have hbridge (q : ℚ) : algebraMap ℚ ℂ q = ((q : ℂ)) := rfl
  have hdeg : (Polynomial.bernoulli n).natDegree ≤ n := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [Polynomial.coeff_bernoulli, ite_eq_right (not_le.mpr hN)]
  have hsum : Polynomial.eval₂ (algebraMap ℚ ℂ) x (Polynomial.bernoulli n) =
      ∑ i ∈ Finset.range (n + 1),
        ((n.choose i : ℕ) : ℂ) * ((bernoulli (n - i) : ℚ) : ℂ) * x ^ i := by
    have hbase := Polynomial.eval₂_eq_sum_range (algebraMap ℚ ℂ) x
      (p := Polynomial.bernoulli n)
    have hext : (∑ i ∈ Finset.range ((Polynomial.bernoulli n).natDegree + 1),
          algebraMap ℚ ℂ ((Polynomial.bernoulli n).coeff i) * x ^ i) =
        ∑ i ∈ Finset.range (n + 1),
          algebraMap ℚ ℂ ((Polynomial.bernoulli n).coeff i) * x ^ i := by
      apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ hdeg))
      intro i _ hi2
      have hlt : (Polynomial.bernoulli n).natDegree < i :=
        lt_of_not_ge (fun h => hi2 (Finset.mem_range.mpr (Nat.lt_succ_of_le h)))
      rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
    rw [hbase, hext]
    apply Finset.sum_congr rfl
    intro i hi
    have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    rw [Polynomial.coeff_bernoulli, ite_eq_left hi']
    rw [map_mul, map_natCast, hbridge]
    ring
  have hrefl := Finset.sum_range_reflect
    (fun k => ((n.choose k : ℕ) : ℂ) * ((bernoulli k : ℚ) : ℂ) * x ^ (n - k)) (n + 1)
  simp only [Nat.add_sub_cancel] at hrefl
  rw [hsum, ← hrefl]
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [Nat.choose_symm hi']
  rw [Nat.sub_sub_self hi']

/-- The Bernoulli polynomial at `1` equals the Bernoulli number, for `n ≠ 1`,
from `bernoulli_eq_bernoulli'_of_ne_one`. -/
private theorem eval₂_bernoulli_one (n : ℕ) (hn : n ≠ 1) :
    (Polynomial.bernoulli n).eval₂ (algebraMap ℚ ℂ) 1 = ((bernoulli n : ℚ) : ℂ) := by
  rw [Polynomial.eval₂_at_one, Polynomial.bernoulli_eval_one,
    ← bernoulli_eq_bernoulli'_of_ne_one hn]
  rfl

/-- **Bernoulli-number expansion of a Bernoulli-polynomial difference.** For every positive
integer $r$ and every $x \in \mathbb{C}$, $\frac{B_{r+1}(x + 1) - B_{r+1}(1)}{r + 1}$ equals
$\frac{1}{r + 1} \sum_{k=0}^{r} \binom{r+1}{k} B_k\, x^{r+1-k} + x^r$, where $B_{r+1}(x)$ is the
Bernoulli polynomial and $B_k$ are the Bernoulli numbers with $B_1 = -\tfrac12$.

Source: Bruce C. Berndt, Ramanujan's Notebooks, Part I, Chapter 7, Entry 8.
Proves `Wanted` entry `ramanujan_part1_ch7_entry8`.
-/
theorem ramanujan_part1_ch7_entry8 (r : ℕ) (hr : 0 < r) (x : ℂ) :
    ((Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) -
      (Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) 1) / (r + 1 : ℂ) =
    (∑ k ∈ range (r + 1),
        ((r + 1).choose k : ℂ) * (bernoulli k : ℂ) * x ^ (r + 1 - k)) /
        (r + 1 : ℂ) + x ^ r := by
  have hn1 : r + 1 ≠ 1 := by omega
  have hr1 : r + 1 - 1 = r := by omega
  have hne : ((r : ℂ) + 1) ≠ 0 := by
    have h : ((r + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    push_cast at h
    exact h
  have hshift := eval₂_bernoulli_shift (r + 1) x
  rw [hr1] at hshift
  have hexp := eval₂_bernoulli_expand (r + 1) x
  have h1 := eval₂_bernoulli_one (r + 1) hn1
  have hpeel : (∑ k ∈ Finset.range (r + 1 + 1),
        (((r + 1).choose k : ℕ) : ℂ) * ((bernoulli k : ℚ) : ℂ) * x ^ (r + 1 - k))
      = (∑ k ∈ Finset.range (r + 1),
        (((r + 1).choose k : ℕ) : ℂ) * ((bernoulli k : ℚ) : ℂ) * x ^ (r + 1 - k))
        + ((bernoulli (r + 1) : ℚ) : ℂ) := by
    rw [Finset.sum_range_succ]
    congr 1
    simp [Nat.choose_self]
  have hnum : (Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) (x + 1) -
      (Polynomial.bernoulli (r + 1)).eval₂ (algebraMap ℚ ℂ) 1 =
      (∑ k ∈ Finset.range (r + 1),
        (((r + 1).choose k : ℕ) : ℂ) * ((bernoulli k : ℚ) : ℂ) * x ^ (r + 1 - k)) +
        ((r + 1 : ℕ) : ℂ) * x ^ r := by
    rw [hshift, h1, hexp, hpeel]
    ring
  have hc : (((r + 1 : ℕ)) : ℂ) = (r : ℂ) + 1 := by push_cast; ring
  rw [hnum, hc]
  field_simp

end

end Entry8

end MathlibExt.Analysis.Ramanujan.Part1Ch7
