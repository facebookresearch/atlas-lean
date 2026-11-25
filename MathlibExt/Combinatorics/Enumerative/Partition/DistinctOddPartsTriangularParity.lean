/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.Enumerative.Partition.Basic
import Mathlib.Algebra.CharP.Algebra
import Mathlib.Algebra.CharP.Lemmas
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.Data.ZMod.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Instances.ZMod
import MathlibExt.Combinatorics.Enumerative.Partition.RamanujanPartitionCongruence

/-!
# Parity of a triangular convolution for partitions with distinct odd parts

Modulo two, Jacobi's cube identity identifies the triangular series with the cube of Euler's
product. The generating function for partitions with unrestricted even parts and distinct odd
parts is the inverse of that cube.
-/

open Finset PowerSeries
open scoped PowerSeries.WithPiTopology

namespace MetaMathlibExt

/-- **Partitions whose odd parts are distinct.** For a natural number $n$, $\mathrm{pod}(n)$ is
the number of partitions of $n$ in which every odd part occurs exactly once; the even parts are
unrestricted.

Its generating function is
$\sum_{n \ge 0} \mathrm{pod}(n) q^n = (-q; q^2)_\infty / (q^2; q^2)_\infty$.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Section 3 (definition of `pod(n)` before Theorem 6). -/
@[expose]
public def distinctOddPartsCount (n : ℕ) : ℕ :=
  ((Finset.univ : Finset n.Partition).filter
    fun p => ∀ i ∈ p.parts, Odd i → p.parts.count i = 1).card

private def podWeight (i c : ℕ) : ZMod 2 := if Even i ∨ c < 2 then 1 else 0

local notation "𝔽" => ZMod 2

private noncomputable abbrev podSeries := Nat.Partition.genFun podWeight

private lemma coeff_podSeries (n : ℕ) : coeff n podSeries = (distinctOddPartsCount n : 𝔽) := by
  simp only [Nat.Partition.coeff_genFun, Finsupp.prod, podWeight]
  simp_rw [prod_boole]
  rw [sum_boole, distinctOddPartsCount]
  congr 2
  ext p
  simp only [mem_filter, mem_univ, true_and, Multiset.toFinsupp_support,
    Multiset.toFinsupp_apply, Multiset.mem_toFinset]
  constructor
  · intro h i hi ho
    have hc := (h i hi).resolve_left (Nat.not_even_iff_odd.mpr ho)
    have := Multiset.one_le_count_iff_mem.mpr hi
    omega
  · intro h i hi
    by_cases he : Even i
    · exact Or.inl he
    · exact Or.inr (by rw [h i hi (Nat.not_even_iff_odd.mp he)]; decide)

private noncomputable def eulerFactor (i : ℕ) : 𝔽⟦X⟧ := 1 - X ^ i

private noncomputable def podFactor (i : ℕ) : 𝔽⟦X⟧ :=
  1 + ∑' j : ℕ, podWeight i (j + 1) • X ^ (i * (j + 1))

private noncomputable def evenFactor (i : ℕ) : 𝔽⟦X⟧ := if Even i then eulerFactor i ^ 2 else 1

private lemma podFactor_mul_evenFactor (i : ℕ) (hi : i ≠ 0) :
    podFactor i * evenFactor i = eulerFactor i := by
  let y := (X : 𝔽⟦X⟧) ^ i
  by_cases he : Even i
  · have hy : constantCoeff y = 0 := by simp [y, hi]
    have hs := WithPiTopology.summable_pow_of_constantCoeff_eq_zero hy
    have hgeom := WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hy
    have h : podFactor i = ∑' j : ℕ, y ^ j := by
      simpa [podFactor, podWeight, he, pow_mul, y] using hs.sum_add_tsum_nat_add 1
    rw [h, evenFactor, ite_eq_left he, eulerFactor, sq, ← mul_assoc, hgeom, one_mul]
  · have h : podFactor i = 1 + X ^ i := by
      unfold podFactor
      rw [tsum_eq_single 0]
      · simp [podWeight]
      · intro j hj
        have hk : ¬ j + 1 < 2 := by omega
        simp [podWeight, he, hk]
    rw [h, evenFactor, ite_eq_right he, mul_one, eulerFactor, sub_eq_add_neg]
    have hneg : (-1 : 𝔽⟦X⟧) = 1 := by
      simpa only [map_neg, map_one] using congrArg (C (R := 𝔽)) (show (-1 : 𝔽) = 1 by decide)
    rw [← neg_one_mul (X ^ i), hneg, one_mul]

private lemma eulerFactor_sq (i : ℕ) : eulerFactor i ^ 2 = eulerFactor (i * 2) := by
  let : CharP 𝔽⟦X⟧ 2 := charP_of_injective_ringHom C_injective 2
  unfold eulerFactor
  rw [sub_pow_char (p := 2), one_pow, pow_mul]

private lemma evenFactor_odd_index (i : ℕ) :
    evenFactor (2 * i + 1 + 1) = eulerFactor (i + 1) ^ 4 := by
  have hEven : Even (2 * i + 1 + 1) := ⟨i + 1, by omega⟩
  have hExp : 2 * i + 1 + 1 = (i + 1) * 2 := by omega
  calc
    evenFactor (2 * i + 1 + 1) = eulerFactor ((i + 1) * 2) ^ 2 := by
      rw [evenFactor, ite_eq_left hEven, hExp]
    _ = (eulerFactor (i + 1) ^ 2) ^ 2 := congrArg (· ^ 2) (eulerFactor_sq (i + 1)).symm
    _ = eulerFactor (i + 1) ^ 4 := (pow_mul _ 2 2).symm

private lemma hasProd_evenFactor :
    HasProd (fun i : ℕ => evenFactor (i + 1)) ((pentagonalSeries 𝔽) ^ 4) := by
  have he : HasProd (fun i : ℕ => evenFactor (2 * i + 1)) 1 := by
    apply hasProd_one.congr_fun
    intro i
    have hi : ¬ Even (2 * i + 1) := by simp [parity_simps]
    exact ite_eq_right hi
  have ho : HasProd (fun i : ℕ => evenFactor (2 * i + 1 + 1)) ((pentagonalSeries 𝔽) ^ 4) :=
    ((WithPiTopology.hasProd_one_sub_X_pow 𝔽).pow 4).congr_fun evenFactor_odd_index
  have h := HasProd.even_mul_odd (f := fun i => evenFactor (i + 1)) he ho
  rwa [one_mul] at h

private lemma pod_mul_euler_cube : podSeries * (pentagonalSeries 𝔽) ^ 3 = 1 := by
  have hp : HasProd (fun i : ℕ => podFactor (i + 1)) podSeries :=
    Nat.Partition.hasProd_genFun podWeight
  have hall := (hp.mul hasProd_evenFactor).congr_fun fun i =>
    (podFactor_mul_evenFactor (i + 1) (Nat.succ_ne_zero i)).symm
  have h := hall.unique (WithPiTopology.hasProd_one_sub_X_pow 𝔽)
  have h0 : pentagonalSeries 𝔽 ≠ 0 := by
    intro he
    have hcoeff := congrArg (coeff (pentagonal 0)) he
    rw [coeff_pentagonalSeries_pentagonal, map_zero, Int.negOnePow_zero, Units.val_one] at hcoeff
    exact one_ne_zero hcoeff
  apply mul_right_cancel₀ h0
  simpa only [one_mul, mul_assoc, ← pow_succ] using h

private lemma map_pentagonalSeries :
    map (Int.castRingHom 𝔽) (pentagonalSeries ℤ) = pentagonalSeries 𝔽 := by
  apply PowerSeries.ext
  intro n
  rw [coeff_map]
  by_cases h : n ∈ Set.range pentagonal
  · obtain ⟨i, rfl⟩ := h
    simp only [coeff_pentagonalSeries_pentagonal, Int.coe_castRingHom, Int.coe_negOnePow,
      Int.cast_pow, Int.cast_neg, Int.cast_one, ZMod.neg_one_eq_one_iff.mpr (Or.inr rfl)]
  · simp [coeff_pentagonalSeries_eq_zero _ h]

private noncomputable abbrev triangularSeries := map (Int.castRingHom 𝔽) jacobiCubeSeries

private lemma triangularSeries_mul_pod : triangularSeries * podSeries = 1 := by
  unfold triangularSeries
  rw [← pentagonalSeries_pow_three, map_pow, map_pentagonalSeries, mul_comm]
  exact pod_mul_euler_cube

private lemma choose_two_succ_eq_triangle (k : ℕ) : (k + 1).choose 2 = k * (k + 1) / 2 := by
  rw [Nat.choose_two_right, Nat.add_sub_cancel, Nat.mul_comm (k + 1) k]

private lemma two_mul_triangle (k : ℕ) : 2 * (k * (k + 1) / 2) = k * (k + 1) := by
  simpa only [choose_two_succ_eq_triangle] using two_mul_choose_two_succ k

private lemma tri_injective : Function.Injective (fun k : ℕ => k * (k + 1) / 2) := by
  refine (show StrictMono (fun k : ℕ => k * (k + 1) / 2) from ?_).injective
  intro a b hab
  nlinarith [two_mul_triangle a, two_mul_triangle b]

private lemma le_triangle (k : ℕ) : k ≤ k * (k + 1) / 2 := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · nlinarith [two_mul_triangle k]

private lemma coeff_triangularSeries_triangle (k : ℕ) :
    coeff (k * (k + 1) / 2) triangularSeries = 1 := by
  rw [← choose_two_succ_eq_triangle, coeff_map, coeff_jacobiCubeSeries_triangle]
  have hneg : (-1 : 𝔽) = 1 := by decide
  have htwo : (2 : 𝔽) = 0 := by decide
  simp [hneg, htwo]

private lemma coeff_triangularSeries_eq_zero {b : ℕ}
    (hb : ∀ k : ℕ, k * (k + 1) / 2 ≠ b) : coeff b triangularSeries = 0 := by
  rw [coeff_map, coeff_jacobiCubeSeries_eq_zero, map_zero]
  simpa only [choose_two_succ_eq_triangle] using hb

/-- **Evenness of a triangular sum of partition counts with distinct odd parts.** Let
$\operatorname{pod}(m)$ be the number of partitions of $m$ in which no odd part is repeated. For
every $n > 0$, the sum $\sum_{k \ge 0} \operatorname{pod}(n - k(k+1)/2)$ over the $k$ with
$k(k+1)/2 \le n$ is even.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Corollary 1 (`integers-2026-A60-cor-1`). -/
public theorem distinctOddParts_triangular_sum_even (n : ℕ) (hn : 0 < n) :
    Even (∑ k ∈ (Finset.range (n + 1)).filter (fun k => k * (k + 1) / 2 ≤ n),
      distinctOddPartsCount (n - k * (k + 1) / 2)) := by
  have h := congrArg (coeff n) triangularSeries_mul_pod
  rw [coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk, coeff_one, ite_eq_right hn.ne'] at h
  change ∑ i ∈ range (n + 1), coeff i triangularSeries * coeff (n - i) podSeries = 0 at h
  rw [← ZMod.natCast_eq_zero_iff_even, Nat.cast_sum]
  refine (sum_of_injOn (fun k => k * (k + 1) / 2) tri_injective.injOn ?_ ?_ ?_).trans h
  · intro k hk
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_filter.mp hk).2)
  · intro i hi hmiss
    rw [coeff_triangularSeries_eq_zero, zero_mul]
    intro k hk
    have hki : k ≤ i := hk ▸ le_triangle k
    have hin : k ∈ range (n + 1) := mem_range.mpr (lt_of_le_of_lt hki (mem_range.mp hi))
    exact hmiss ⟨k, mem_filter.mpr ⟨hin, hk ▸ Nat.le_of_lt_succ (mem_range.mp hi)⟩, hk⟩
  · intro k _
    rw [coeff_triangularSeries_triangle, one_mul, coeff_podSeries]

end MetaMathlibExt
