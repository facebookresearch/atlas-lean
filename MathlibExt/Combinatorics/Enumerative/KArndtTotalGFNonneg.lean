/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.KArndtRecurrence

/-!
# Generating function of generalized Arndt compositions for nonnegative shifts

The recurrence for the total count gives the ordinary generating function for every nonnegative
shift, including the ordinary Arndt compositions at shift zero.
-/

namespace MetaMathlibExt

namespace kArndtComposition_total_gf_nonneg

private lemma initial (k : ℕ) :
    kArndtTotalCount k 0 = 1 ∧ kArndtTotalCount k 1 = 1 ∧ kArndtTotalCount k 2 = 1 := by
  have pairs : Finset.Nat.antidiagonalTuple 2 2 = {![0, 2], ![1, 1], ![2, 0]} := by decide
  simp [kArndtTotalCount, kArndtCompositionCount, Finset.sum_range_succ, pairs,
    Fin.forall_fin_succ, Finset.filter_insert, Finset.filter_singleton]

end kArndtComposition_total_gf_nonneg

open PowerSeries kArndtComposition_total_gf_nonneg in
/-- **Counting $k$-Arndt compositions for nonnegative $k$.** Let $k \ge 0$ be an integer and let
$a_k(n) = \sum_{m = 0}^{n} a_k(n, m)$ be the number of $k$-Arndt compositions of $n$. Then, in
$\mathbb{Z}[[x]]$,
$$\Bigl(\sum_{n \ge 0} a_k(n)\, x^n\Bigr)(1 - x - x^2 + x^3 - x^{k+3}) = 1 - x^2,$$
that is, $\sum_{n \ge 0} a_k(n)\, x^n = (1 - x^2)/(1 - x - x^2 + x^3 - x^{k+3})$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 6, case `k ≥ 0`
(`integers-2024-A35-cor-6`). -/
public theorem kArndtComposition_total_gf_nonneg (k : ℕ) :
    (PowerSeries.mk fun n =>
        ((∑ m ∈ Finset.range (n + 1), kArndtCompositionCount k n m : ℕ) : ℤ)) *
        (1 - PowerSeries.X - PowerSeries.X ^ 2 + PowerSeries.X ^ 3 - PowerSeries.X ^ (k + 3)) =
      1 - PowerSeries.X ^ 2 := by
  let A : PowerSeries ℤ := mk fun n ↦ (kArndtTotalCount k n : ℤ)
  change A * _ = _
  simp only [mul_sub, mul_add, mul_one]
  rw [show A * X = A * X ^ 1 by rw [pow_one]]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_one, coeff_X_pow, A, coeff_mk]
  obtain ⟨h₀, h₁, h₂⟩ := initial k
  rcases n with _ | _ | _ | n
  · simp [h₀]
  · simp [h₀, h₁]
  · simp [h₀, h₁, h₂]
  · have h := kArndtTotalCount_recurrence.2 k (n + 3) (by omega)
    rw [Nat.sub_sub, Nat.add_comm 3 k] at h
    simp only [ite_eq_left (show 1 ≤ n + 3 by omega), ite_eq_left (show 2 ≤ n + 3 by omega),
      ite_eq_left (show 3 ≤ n + 3 by omega), ite_eq_right (show n + 3 ≠ 0 by omega),
      ite_eq_right (show n + 3 ≠ 2 by omega)]
    rw [h]
    abel

end MetaMathlibExt
