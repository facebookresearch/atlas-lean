/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.Enumerative.Partition.MercaDistinctPartsSum
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import all MathlibExt.Combinatorics.Enumerative.Partition.MercaSignedTriangularSum
import all MathlibExt.Combinatorics.Enumerative.Partition.MercaTwiceSquareSum
import all MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionCongruence

/-!
# Merca's signed square identity

We use Ballantine's reduction to the ordinary partition generating function. We reuse the
formalization of Gauss's signed-square product in `OverpartitionCongruence`. The product
left after cancellation is the generating function for partitions weighted by the parity of their
number of parts.

## References

* Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
  Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
  Article A15, pp. 3–5, Theorem 2.
* Mircea Merca, *Linear inequalities concerning the sum of the distinct parts congruent to r
  modulo m in all the partitions of n*, Quaestiones Mathematicae 46 (2023), pp. 2637–2659,
  Corollary 4.2.
* George E. Andrews, *Two theorems of Gauss and allied identities proved arithmetically*,
  Pacific Journal of Mathematics 41 (1972), pp. 563–578, equation (1.4).
* Carl Friedrich Gauss, *Werke*, vol. 3, Königliche Gesellschaft der Wissenschaften,
  Göttingen (1866), p. 447, equation (10), as cited by Andrews.
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

namespace sumDistinctPartsModEq_square_eq_evenOdd

open sumDistinctPartsModEq_triangular_eq_distinct_half
open sumDistinctPartsModEq_twiceSquare_eq_oddDistinct

private lemma square_injective : Function.Injective (fun k : ℕ => k ^ 2) := by
  intro a b h
  change a ^ 2 = b ^ 2 at h
  exact twiceSquare_injective (congrArg (2 * ·) h)

private lemma le_square (k : ℕ) : k ≤ k ^ 2 := Nat.le_self_pow two_ne_zero k

private noncomputable def signedSquare : ℤ⟦X⟧ := indexedSeries (fun k => k ^ 2) weight

private lemma card_squareFiber (k : ℕ) :
    Nat.card {x : ℤ // x.natAbs ^ 2 = k ^ 2} = if k = 0 then 1 else 2 := by
  let s : Finset ℤ := {(k : ℤ), -(k : ℤ)}
  have h (x : ℤ) : x.natAbs ^ 2 = k ^ 2 ↔ x ∈ s := by
    simp only [s, mem_insert, mem_singleton]
    constructor
    · intro hx
      have hk := square_injective hx
      simpa only [hk] using Int.natAbs_eq x
    · rintro (rfl | rfl) <;> simp
  rw [Nat.card_congr (Equiv.subtypeEquivRight h), Nat.card_eq_fintype_card, Fintype.card_coe]
  by_cases hk : k = 0
  · simp [s, hk]
  · rw [ite_eq_right hk, card_pair_eq_two_iff]
    omega

private lemma rescale_opcTheta : rescale (-1) opcTheta = signedSquare := by
  ext n
  rw [coeff_rescale, opc_theta_coeff_eq_card, signedSquare]
  by_cases hn : n ∈ Set.range (fun k : ℕ => k ^ 2)
  · obtain ⟨k, rfl⟩ := hn
    rw [coeff_indexedSeries_at square_injective le_square, card_squareFiber]
    have hs : (-1 : ℤ) ^ (k ^ 2) = (-1) ^ k :=
      neg_one_pow_congr (by simp [pow_two, Nat.even_mul])
    by_cases hk : k = 0
    · subst k
      simp [weight]
    · simp [hs, weight, hk, mul_comm]
  · have hempty : IsEmpty {x : ℤ // x.natAbs ^ 2 = n} :=
      ⟨fun x => hn ⟨x.val.natAbs, x.property⟩⟩
    rw [coeff_indexedSeries_off _ hn, Nat.card_eq_zero.mpr (Or.inl hempty),
      Nat.cast_zero, mul_zero]

private lemma signedSquare_mul_euler_two :
    signedSquare * qEulerProduct 2 = qEulerProduct 1 ^ 2 := by
  rw [← rescale_opcTheta, eulerSeries_eq_expand 2 two_ne_zero, qEulerProduct_one]
  exact phiFiveCoreAnalog_five_pow_mul.theta_euler_product opcTheta opc_theta_coeff_eq_card

private noncomputable def signedPartitions : ℤ⟦X⟧ :=
  Nat.Partition.genFun (fun _ c => (-1 : ℤ) ^ c)

private lemma coeff_signedPartitions (n : ℕ) : signedPartitions.coeff n =
    ∑ μ : Nat.Partition n, (-1 : ℤ) ^ μ.parts.card := by
  rw [signedPartitions, Nat.Partition.coeff_genFun]
  refine sum_congr rfl fun μ _ => ?_
  rw [Finsupp.prod, prod_pow_eq_pow_sum, ← Multiset.toFinsupp_sum_eq]
  rfl

private lemma signedPartitionFactor_mul (i : ℕ) :
    ((1 : ℤ⟦X⟧) + ∑' j : ℕ, (-1 : ℤ) ^ (j + 1) • X ^ ((i + 1) * (j + 1))) *
      (1 - X ^ (2 * (i + 1))) = 1 - X ^ (i + 1) := by
  let x : ℤ⟦X⟧ := X ^ (i + 1)
  have hx : (-x).constantCoeff = 0 := by simp [x, pow_succ, map_mul]
  have hs := WithPiTopology.summable_pow_of_constantCoeff_eq_zero hx
  have h := hs.tsum_pow_mul_one_sub
  rw [sub_neg_eq_add] at h
  have hsum : (∑' j : ℕ, (-x) ^ j) =
      1 + ∑' j : ℕ, (-1 : ℤ) ^ (j + 1) • X ^ ((i + 1) * (j + 1)) := by
    rw [hs.tsum_eq_zero_add, pow_zero]
    congr 1
    apply tsum_congr
    intro j
    have hc (a : ℤ) : C a = (a : ℤ⟦X⟧) := by
      simpa only [Int.cast_id] using map_intCast (C : ℤ →+* ℤ⟦X⟧) a
    rw [show -x = C (-1 : ℤ) * x by simp, mul_pow, ← map_pow, zsmul_eq_mul, hc]
    simp only [x, pow_mul]
  rw [← hsum, mul_comm 2 (i + 1), pow_mul, pow_two]
  change (∑' j : ℕ, (-x) ^ j) * (1 - x * x) = 1 - x
  rw [show 1 - x * x = (1 + x) * (1 - x) by ring, ← mul_assoc, h, one_mul]

private lemma signedPartitions_mul_euler_two :
    signedPartitions * qEulerProduct 2 = qEulerProduct 1 := by
  have h := (Nat.Partition.hasProd_genFun (fun _ c => (-1 : ℤ) ^ c)).mul
    (hasProd_eulerSeries 2 two_ne_zero)
  exact (h.congr_fun fun i => (signedPartitionFactor_mul i).symm).unique
    ((hasProd_eulerSeries 1 one_ne_zero).congr_fun fun i => by rw [one_mul])

private lemma signedSquare_mul_partitions : signedSquare * partitions = signedPartitions := by
  have hne : qEulerProduct 2 ≠ 0 := by
    intro h
    have he := congrArg constantCoeff h
    simp [constantCoeff_qEulerProduct (by decide : 1 ≤ 2)] at he
  apply mul_right_cancel₀ hne
  calc
    (signedSquare * partitions) * qEulerProduct 2 = partitions * qEulerProduct 1 ^ 2 := by
      rw [mul_comm signedSquare, mul_assoc, signedSquare_mul_euler_two]
    _ = (partitions * qEulerProduct 1) * qEulerProduct 1 := by rw [pow_two, mul_assoc]
    _ = signedPartitions * qEulerProduct 2 := by
      rw [partitions_mul_euler, one_mul, signedPartitions_mul_euler_two]

end sumDistinctPartsModEq_square_eq_evenOdd

open sumDistinctPartsModEq_square_eq_evenOdd sumDistinctPartsModEq_triangular_eq_distinct_half
  sumDistinctPartsModEq_twiceSquare_eq_oddDistinct in
/-- **Different parts in a residue class and even-minus-odd partition counts.** Let $m$, $r$ and
$n$ be natural numbers with $r < m$, and for $k \ge 0$ let $a_{r,m}(k)$ be the sum, over all
partitions of $k$, of the different parts congruent to $r$ modulo $m$, each counted once per
partition whatever its multiplicity. Let $p_{e-o}(k) = \sum_{\mu} (-1)^{\ell(\mu)}$, the sum over
the partitions $\mu$ of $k$ with $\ell(\mu)$ the number of parts of $\mu$; it is the number of
partitions of $k$ with an even number of parts minus the number with an odd number of parts. Then
$$a_{r,m}(n) + 2 \sum_{k \ge 1,\ k^2 \le n} (-1)^k a_{r,m}(n - k^2)
= \sum_{j \ge 0,\ mj + r \le n} (mj + r)\, p_{e-o}(n - mj - r).$$

Source: Cristina Ballantine, *Combinatorial Proofs of Merca's Identities Involving the Sum of
Different Parts Congruent to r Modulo m in All Partitions of n*, INTEGERS 24 (2024),
Article A15, Theorem 2 (`integers-2024-A15-thm-2`). -/
public theorem sumDistinctPartsModEq_square_eq_evenOdd (m r n : ℕ) (hrm : r < m) :
    (sumDistinctPartsModEq m r n : ℤ)
        + 2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => k ^ 2 ≤ n),
          (-1 : ℤ) ^ k * (sumDistinctPartsModEq m r (n - k ^ 2) : ℤ)
      = ∑ j ∈ (Finset.range (n + 1)).filter (fun j => m * j + r ≤ n),
          ((m * j + r : ℕ) : ℤ) *
            ∑ μ : Nat.Partition (n - (m * j + r)), (-1 : ℤ) ^ μ.parts.card := by
  have h : signedSquare * (progression m r * partitions) = progression m r * signedPartitions := by
    rw [← signedSquare_mul_partitions]
    ac_rfl
  have hc := congrArg (coeff n) h
  rw [signedSquare, coeff_indexedSeries_mul square_injective le_square,
    coeff_progression_mul m r n hrm] at hc
  simp only [coeff_progression_mul_partitions m r _ hrm, coeff_signedPartitions] at hc
  refine Eq.trans ?_ hc
  let s := (range (n + 1)).filter (fun k => k ^ 2 ≤ n)
  let f (k : ℕ) : ℤ := weight k * (sumDistinctPartsModEq m r (n - k ^ 2) : ℤ)
  change _ = ∑ k ∈ s, f k
  have h0 : 0 ∈ s := by simp [s]
  have hhead : f 0 = (sumDistinctPartsModEq m r n : ℤ) := by simp [f, weight]
  have hs : s.erase 0 = (Icc 1 n).filter (fun k => k ^ 2 ≤ n) := by
    ext k
    simp only [s, mem_erase, mem_filter, mem_range_succ_iff, mem_Icc]
    omega
  rw [← add_sum_erase s f h0, hhead, hs, mul_sum]
  congr 1
  exact sum_congr rfl fun k hk => by
    have hk0 := Nat.ne_of_gt (mem_Icc.mp (mem_filter.mp hk).1).1
    simp [f, weight, hk0, mul_assoc]

end MetaMathlibExt
