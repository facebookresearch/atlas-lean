/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.RingTheory.PowerSeries.Basic
public import MathlibExt.Combinatorics.Enumerative.KArndtRecurrence
import Mathlib.Tactic.Ring

/-!
# Generating function of generalized Arndt compositions for negative shifts

The negative-shift recurrence for the total counts gives their ordinary generating function.
-/

namespace MetaMathlibExt

namespace kArndtComposition_total_gf_neg

private lemma initial (j : ℕ) (hj : 0 < j) :
    kArndtTotalCount (-(j : ℤ)) 0 = 1 ∧ kArndtTotalCount (-(j : ℤ)) 1 = 1 ∧
      kArndtTotalCount (-(j : ℤ)) 2 = 2 := by
  have pairs : Finset.Nat.antidiagonalTuple 2 2 = {![0, 2], ![1, 1], ![2, 0]} := by decide
  simp [kArndtTotalCount, kArndtCompositionCount, Finset.sum_range_succ, pairs,
    Fin.forall_fin_succ, Finset.filter_insert, Finset.filter_singleton, hj]

end kArndtComposition_total_gf_neg

open PowerSeries kArndtComposition_total_gf_neg in
/-- **Counting $k$-Arndt compositions for negative $k$.** Let $k = -k'$ with $k' \ge 1$ an integer,
and let $a_k(n) = \sum_{m = 0}^{n} a_k(n, m)$ be the number of $k$-Arndt compositions of $n$. Then,
in $\mathbb{Z}[[x]]$,
$$\Bigl(\sum_{n \ge 0} a_k(n)\, x^n\Bigr)(1 - x - 2x^2 + x^{2-k}) = 1 - x^2,$$
that is, $\sum_{n \ge 0} a_k(n)\, x^n = (1 - x^2)/(1 - x - 2x^2 + x^{2-k})$.

Source: Daniel F. Checa and José L. Ramírez, *Arndt Compositions: A Generating Functions
Approach*, INTEGERS 24 (2024), Article A35, Corollary 6, case `k < 0`
(`integers-2024-A35-cor-6`). -/
public theorem kArndtComposition_total_gf_neg (k' : ℕ) (hk' : 0 < k') :
    (PowerSeries.mk fun n =>
        ((∑ m ∈ Finset.range (n + 1), kArndtCompositionCount (-(k' : ℤ)) n m : ℕ) : ℤ)) *
        (1 - PowerSeries.X - 2 * PowerSeries.X ^ 2 + PowerSeries.X ^ (2 + k')) =
      1 - PowerSeries.X ^ 2 := by
  let A : PowerSeries ℤ := mk fun n ↦ (kArndtTotalCount (-(k' : ℤ)) n : ℤ)
  change A * _ = _
  rw [show A * (1 - X - 2 * X ^ 2 + X ^ (2 + k')) =
    A - A * X ^ 1 - (A * X ^ 2 + A * X ^ 2) + A * X ^ (2 + k') by ring]
  ext n
  simp only [map_add, map_sub, coeff_mul_X_pow', coeff_one, coeff_X_pow, A, coeff_mk]
  obtain ⟨h₀, h₁, h₂⟩ := initial k' hk'
  rcases n with _ | _ | _ | n
  · simp [h₀]
  · simp [h₀, h₁, show ¬ 2 + k' ≤ 1 by omega]
  · simp [h₀, h₁, h₂, show ¬ 2 + k' ≤ 2 by omega]
  · have h := kArndtTotalCount_recurrence.1 k' (n + 3) (by omega)
    rw [Nat.sub_sub, Nat.add_comm k' 2] at h
    simp only [ite_eq_left (show 1 ≤ n + 3 by omega), ite_eq_left (show 2 ≤ n + 3 by omega),
      ite_eq_right (show n + 3 ≠ 0 by omega), ite_eq_right (show n + 3 ≠ 2 by omega)]
    rw [h]
    ring

end MetaMathlibExt
