/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.BigOperators.Intervals
public import MathlibExt.NumberTheory.LucasSequence
import Mathlib.Algebra.BigOperators.NatAntidiagonal
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Tactic.Ring
import MathlibExt.NumberTheory.Recurrences.LucasSequenceAddition

/-!
# Lucas convolution with shifted binomial weights

Binomial symmetry changes the shifted index `n + k` to `n - k`. The two weights then swap
under reflection, so the Lucas addition formula evaluates the sum of each reflected pair.
Vandermonde's identity evaluates the sum of the weights.
-/

namespace MetaMathlibExt

open Finset
open MathlibExt.NumberTheory.Recurrences.KruchininPerminovaHadamardWanted (two_mul_lucasU_add)

set_option backward.proofsInPublic true in
/-- **Convolution of U and V with shifted binomial weights.** Let $p$ be an integer and let $U$ and
$V$ be the Lucas sequences $U(p, -1)$ and $V(p, -1)$, so that $U_0 = 0$, $U_1 = 1$, $V_0 = 2$,
$V_1 = p$, and both satisfy $X_{j+2} = p X_{j+1} + X_j$. Then for every natural number $n$
$$\sum_{k=0}^{n} \binom{2n}{k} \binom{2n}{n+k} U_k V_{n-k} = \binom{4n}{n} U_n.$$

Source: John M. Campbell and Emrah Kılıç, *Binomial Sums Involving Second-Order Linearly Recurrent
Sequences*, The Fibonacci Quarterly 62 (2024), Article 62-1/campbell10202023, Proposition 2.6. -/
public theorem lucasU_lucasV_sum_choose_two_n (p : ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
        ((2 * n).choose k * (2 * n).choose (n + k) : ℤ) *
          lucasU ⟨p, -1, by decide⟩ k * lucasV ⟨p, -1, by decide⟩ (n - k) =
      ((4 * n).choose n : ℤ) * lucasU ⟨p, -1, by decide⟩ n := by
  let P : LucasSequenceParams := ⟨p, -1, by decide⟩
  let w (k : ℕ) : ℤ := ((2 * n).choose k : ℤ) * (2 * n).choose (n - k)
  have hshift : ∑ k ∈ range (n + 1),
      ((2 * n).choose k * (2 * n).choose (n + k) : ℤ) * lucasU P k * lucasV P (n - k) =
      ∑ k ∈ range (n + 1), w k * lucasU P k * lucasV P (n - k) := by
    refine sum_congr rfl fun k hk => ?_
    have hkn := mem_range_succ_iff.mp hk
    have hchoose := Nat.choose_symm (show n + k ≤ 2 * n by omega)
    rw [show 2 * n - (n + k) = n - k by omega] at hchoose
    simp only [← hchoose, w]
  have hweights : ∑ k ∈ range (n + 1), w k = ((4 * n).choose n : ℤ) := by
    have h : ∑ k ∈ range (n + 1), (2 * n).choose k * (2 * n).choose (n - k) =
        (4 * n).choose n := by
      rw [show 4 * n = 2 * n + 2 * n by omega, Nat.add_choose_eq,
        Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    simpa only [Nat.cast_sum, Nat.cast_mul, w] using congrArg (fun m : ℕ => (m : ℤ)) h
  change (∑ k ∈ range (n + 1),
    ((2 * n).choose k * (2 * n).choose (n + k) : ℤ) * lucasU P k * lucasV P (n - k)) = _
  rw [hshift, ← hweights]
  have hreflect : ∑ k ∈ range (n + 1), w k * lucasU P k * lucasV P (n - k) =
      ∑ k ∈ range (n + 1), w k * lucasU P (n - k) * lucasV P k := by
    rw [← sum_range_reflect]
    refine sum_congr rfl fun k hk => ?_
    simp only [Nat.add_sub_cancel, Nat.sub_sub_self (mem_range_succ_iff.mp hk), w]
    ring
  apply mul_left_cancel₀ (two_ne_zero (α := ℤ))
  calc
    2 * ∑ k ∈ range (n + 1), w k * lucasU P k * lucasV P (n - k) =
        (∑ k ∈ range (n + 1), w k * lucasU P k * lucasV P (n - k)) +
          ∑ k ∈ range (n + 1), w k * lucasU P (n - k) * lucasV P k := by
      rw [two_mul, ← hreflect]
    _ = ∑ k ∈ range (n + 1), w k * (2 * lucasU P n) := by
      rw [← sum_add_distrib]
      refine sum_congr rfl fun k hk => ?_
      have hadd := two_mul_lucasU_add P k (n - k)
      rw [Nat.add_sub_of_le (mem_range_succ_iff.mp hk)] at hadd
      rw [hadd]
      ring
    _ = 2 * ((∑ k ∈ range (n + 1), w k) * lucasU P n) := by
      rw [← sum_mul]
      ring

end MetaMathlibExt
