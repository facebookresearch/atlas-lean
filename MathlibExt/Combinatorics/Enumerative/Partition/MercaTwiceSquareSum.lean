/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.MercaDistinctPartsSum
import Mathlib.Combinatorics.Enumerative.Pentagonal.EulerFunction
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import MathlibExt.Combinatorics.Enumerative.Partition.QEulerProduct
import all MathlibExt.Combinatorics.Enumerative.Partition.EulerQuotientThreeDissection
import all MathlibExt.Combinatorics.Enumerative.Partition.MercaSignedTriangularSum
import all MathlibExt.Combinatorics.Enumerative.Partition.OddDistinctsPentagonalRecurrence

/-!
# Merca's twice-square identity

We use Ballantine's reduction to the ordinary partition generating function. Instead of
using sign-reversing involutions for the resulting convolution, we specialize the Jacobi
triple product and use the generating function for partitions into distinct odd parts.

## References

* Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
  Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
  Article A15, pp. 6–7, Theorem 4 and equation (7).
* Mircea Merca, *Linear inequalities concerning the sum of the distinct parts congruent to r
  modulo m in all the partitions of n*, Quaestiones Mathematicae 46 (2023), pp. 2637–2659,
  Corollary 4.6.
* Aritram Dhar, Avi Mukhopadhyay, and Rishabh Sarma, *Generalization of the Extended Minimal
  Excludant of Andrews and Newman*, Journal of Integer Sequences 26 (2023), Article 23.3.7,
  p. 11, Theorem 21 (Jacobi's triple product).
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

namespace sumDistinctPartsModEq_twiceSquare_eq_oddDistinct

open sumDistinctPartsModEq_triangular_eq_distinct_half

private def twiceSquare (k : ℕ) : ℕ := 2 * k ^ 2

private lemma twiceSquare_injective : Function.Injective twiceSquare := by
  apply StrictMono.injective
  intro a b hab
  simpa only [twiceSquare] using Nat.mul_lt_mul_of_pos_left (pow_lt_pow_left₀ hab (Nat.zero_le a)
    (by decide : (2 : ℕ) ≠ 0)) (by decide : 0 < (2 : ℕ))

private lemma le_twiceSquare (k : ℕ) : k ≤ twiceSquare k :=
  (Nat.le_self_pow (by decide : 2 ≠ 0) k).trans (by simp [twiceSquare, two_mul])

private def weight (k : ℕ) : ℤ := if k = 0 then 1 else 2 * (-1) ^ k

private noncomputable def signedTwiceSquare : ℤ⟦X⟧ := indexedSeries twiceSquare weight

private lemma hasSum_signedTwiceSquare {q : ℂ} (hq : ‖q‖ < 1) :
    HasSum (fun n : ℕ => (signedTwiceSquare.coeff n : ℂ) * q ^ n)
      (eulerFunction (q ^ 2) ^ 2 / eulerFunction (q ^ 4)) := by
  have hs := qEulerProduct_sq_div_three_dissection.square_sum (norm_pow_lt hq two_ne_zero)
  rw [← pow_mul, show (2 : ℕ) * 2 = 4 by decide] at hs
  let term (z : ℤ) : ℂ := (-1 : ℂ) ^ z * (q ^ 2) ^ (z * z)
  change HasSum term _ at hs
  have hneg (k : ℕ) : term (-(k : ℤ)) = term k := by
    simp only [term, neg_mul_neg, zpow_neg, ← inv_zpow, inv_neg, inv_one]
  have hterm (k : ℕ) : term k = (-1 : ℂ) ^ k * q ^ twiceSquare k := by
    have hexp : (k : ℤ) * (k : ℤ) = ((k ^ 2 : ℕ) : ℤ) := by push_cast; ring
    simp only [term, hexp, zpow_natCast, ← pow_mul, twiceSquare]
  -- Pair the positive and negative indices, and count the zero index just once.
  have hp := hs.nat_add_neg.sub (hasSum_ite_eq (0 : ℕ) (1 : ℂ))
  have hzero : term 0 = 1 := by simp [term]
  rw [hzero, add_sub_cancel_right] at hp
  apply (twiceSquare_injective.hasSum_iff ?_).mp
  · refine hp.congr_fun fun k => ?_
    simp only [Function.comp_apply, signedTwiceSquare,
      coeff_indexedSeries_at twiceSquare_injective le_twiceSquare, hneg, hterm]
    by_cases hk : k = 0
    · subst k
      norm_num [weight, twiceSquare]
    · simp only [weight, ite_eq_right hk, sub_zero, Int.cast_mul, Int.cast_ofNat,
        Int.cast_pow, Int.cast_neg, Int.cast_one]
      ring
  · intro n hn
    simp [signedTwiceSquare, coeff_indexedSeries_off _ hn]

private lemma signedTwiceSquare_mul_euler_four :
    signedTwiceSquare * qEulerProduct 4 = qEulerProduct 2 ^ 2 := by
  have hT : Represents signedTwiceSquare
      (fun q => eulerFunction (q ^ 2) ^ 2 / eulerFunction (q ^ 4)) :=
    fun τ => hasSum_signedTwiceSquare (Function.Periodic.norm_qParam_lt_one one_pos τ.im_pos)
  have h₂ := represents_euler 2 two_ne_zero
  have h₄ := represents_euler 4 (by decide)
  have h₂sq : Represents (qEulerProduct 2 ^ 2) (fun q => eulerFunction (q ^ 2) ^ 2) := by
    simpa only [pow_two] using h₂.mul h₂
  exact (hT.mul h₄).eq_of_eval h₂sq fun q hq =>
    div_mul_cancel₀ _ (oddDistincts_pentagonal_recurrence.euler_ne
      (norm_pow_lt hq (by decide : (4 : ℕ) ≠ 0)))

open oddDistincts_pentagonal_recurrence (Dser formal_D)

private lemma signedTwiceSquare_mul_partitions : signedTwiceSquare * partitions = Dser := by
  have h₄ : qEulerProduct 4 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [constantCoeff_qEulerProduct (by decide : 1 ≤ 4)] at h'
  apply mul_right_cancel₀ h₄
  calc
    (signedTwiceSquare * partitions) * qEulerProduct 4 = partitions * qEulerProduct 2 ^ 2 := by
      rw [mul_comm signedTwiceSquare, mul_assoc, signedTwiceSquare_mul_euler_four]
    _ = (partitions * qEulerProduct 1) * (Dser * qEulerProduct 4) := by
      rw [← formal_D]
      ac_rfl
    _ = Dser * qEulerProduct 4 := by rw [partitions_mul_euler, one_mul]

end sumDistinctPartsModEq_twiceSquare_eq_oddDistinct

open sumDistinctPartsModEq_twiceSquare_eq_oddDistinct
  sumDistinctPartsModEq_triangular_eq_distinct_half in
/-- **Twice-square sum of $a_{r,m}$ and distinct odd parts.** Let $m, r, n$ be natural numbers
with $r < m$. Write $a_{r,m}(k)$ for the sum of the different parts congruent to $r$ modulo $m$
in all partitions of $k$, and $q_{\mathrm{odd}}(k)$ for the number of partitions of $k$ into
distinct odd parts. Then
$$
a_{r,m}(n) + 2 \sum_{k \ge 1,\ 2k^2 \le n} (-1)^k a_{r,m}(n - 2k^2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, q_{\mathrm{odd}}(n - mj - r).
$$

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 4 (`integers-2024-A15-thm-4`). -/
public theorem sumDistinctPartsModEq_twiceSquare_eq_oddDistinct (m r n : ℕ)
    (hrm : r < m) :
    (sumDistinctPartsModEq m r n : ℤ)
        + 2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 2 * k ^ 2 ≤ n),
          (-1 : ℤ) ^ k * (sumDistinctPartsModEq m r (n - 2 * k ^ 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) * ((Nat.Partition.oddDistincts (n - (m * j + r))).card : ℤ) := by
  have h : signedTwiceSquare * (progression m r * partitions) =
      progression m r * oddDistincts_pentagonal_recurrence.Dser := by
    rw [← signedTwiceSquare_mul_partitions]
    ac_rfl
  have hc := congrArg (coeff n) h
  rw [signedTwiceSquare, coeff_indexedSeries_mul twiceSquare_injective le_twiceSquare,
    coeff_progression_mul m r n hrm] at hc
  simp only [coeff_progression_mul_partitions m r _ hrm,
    oddDistincts_pentagonal_recurrence.Dser, coeff_mk] at hc
  refine Eq.trans ?_ hc
  let s := (range (n + 1)).filter (fun k => twiceSquare k ≤ n)
  let f (k : ℕ) : ℤ := weight k * (sumDistinctPartsModEq m r (n - twiceSquare k) : ℤ)
  change _ = ∑ k ∈ s, f k
  have h0 : 0 ∈ s :=
    mem_filter.mpr ⟨mem_range_succ_iff.mpr (Nat.zero_le n), by simp [twiceSquare]⟩
  have hhead : f 0 = (sumDistinctPartsModEq m r n : ℤ) := by simp [f, weight, twiceSquare]
  have hs : s.erase 0 = (Icc 1 n).filter (fun k => 2 * k ^ 2 ≤ n) := by
    ext k
    constructor
    · intro hk
      obtain ⟨hk0, hk⟩ := mem_erase.mp hk
      obtain ⟨hkn, hdeg⟩ := mem_filter.mp hk
      exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.pos_of_ne_zero hk0, mem_range_succ_iff.mp hkn⟩,
        hdeg⟩
    · intro hk
      obtain ⟨hk, hdeg⟩ := mem_filter.mp hk
      obtain ⟨hk1, hkn⟩ := mem_Icc.mp hk
      exact mem_erase.mpr ⟨Nat.ne_of_gt hk1,
        mem_filter.mpr ⟨mem_range_succ_iff.mpr hkn, hdeg⟩⟩
  rw [← add_sum_erase s f h0, hhead, hs, mul_sum]
  congr 1
  exact sum_congr rfl fun k hk => by
    have hk0 := Nat.ne_of_gt ((mem_Icc.mp (mem_filter.mp hk).1).1 : 0 < k)
    change _ = weight k * _
    rw [weight, ite_eq_right hk0, twiceSquare, mul_assoc]

end MetaMathlibExt
