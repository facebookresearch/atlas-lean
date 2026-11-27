/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.SetTheory.Cardinal.Finite
public import MathlibExt.Combinatorics.Enumerative.Partition.Overpartition
import Mathlib.Combinatorics.Enumerative.Partition.GenFun
import Mathlib.RingTheory.PowerSeries.Expand
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import MathlibExt.Combinatorics.Enumerative.Partition.OverpartitionCongruence

/-!
# Square recurrence for overpartitions into odd parts

The odd-part overpartition generating function times the square theta series at `-X²`
is the square theta series at `X`. Comparing coefficients gives
`MetaMathlibExt.overpartitionOdd_square_recurrence`.
-/

namespace MetaMathlibExt

/-- **Overpartitions into odd parts.** For a natural number $n$, $\mathrm{po}(n)$ is the
number of overpartitions of $n$ all of whose parts are odd.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, title and Section 1 (values `po(0), …, po(10)`
listed after Theorem 5). -/
@[expose] public noncomputable def overpartitionOddPartsCount (n : ℕ) : ℕ :=
  Nat.card {O : Nat.Overpartition n // ∀ a ∈ O.toPartition.parts, Odd a}

/-- **Overpartitions of zero into odd parts.** The number $\mathrm{po}(0)$ of overpartitions
of $0$ into odd parts equals $1$: the empty overpartition is the only one.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, value `po(0) = 1` listed after Theorem 5. -/
public theorem overpartitionOddPartsCount_zero : overpartitionOddPartsCount 0 = 1 := by
  unfold overpartitionOddPartsCount
  rw [Nat.card_eq_one_iff_exists]
  refine ⟨⟨Nat.Overpartition.ofPartition default, fun a ha => ?_⟩, fun y => ?_⟩
  · simp [Nat.Overpartition.ofPartition_toPartition, Nat.Partition.partition_zero_parts] at ha
  · exact Subtype.ext (Nat.Overpartition.eq_of_zero _ _)

namespace overpartitionOdd_square_recurrence

open PowerSeries
open scoped PowerSeries.WithPiTopology

private noncomputable abbrev oddSeries :=
  Nat.Partition.genFun (fun i _ => if Odd i then (2 : ℤ) else 0)

private noncomputable abbrev allSeries := Nat.Partition.genFun (fun _ _ => (2 : ℤ))

/-- Each distinct size in an odd partition may be overlined independently. -/
private theorem coeff_oddSeries (n : ℕ) : oddSeries.coeff n = overpartitionOddPartsCount n := by
  classical
  let eligible (p : n.Partition) := ∀ a ∈ p.parts, Odd a
  let e : {O : Nat.Overpartition n // eligible O.toPartition} ≃
      Σ p : n.Partition, {s : ↥p.parts.toFinset.powerset // eligible p} :=
    { toFun := fun ⟨O, h⟩ => ⟨O.toPartition, ⟨⟨O.overlines,
        Finset.mem_powerset.mpr O.overlines_subset⟩, h⟩⟩
      invFun := fun ⟨p, s, h⟩ => ⟨⟨p, s, Finset.mem_powerset.mp s.property⟩, h⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [overpartitionOddPartsCount, Nat.card_congr e, Nat.card_sigma, Nat.cast_sum,
    Nat.Partition.coeff_genFun]
  apply Finset.sum_congr rfl
  intro p _
  simp only [Finsupp.prod, Multiset.toFinsupp_support]
  by_cases h : eligible p
  · rw [Finset.prod_congr rfl (g := fun _ => (2 : ℤ))
        (fun a ha => ite_eq_left (h a (Multiset.mem_toFinset.mp ha)))]
    simp [h, Nat.card_eq_fintype_card]
  · obtain ⟨a, ha, ho⟩ : ∃ a ∈ p.parts, ¬ Odd a := by simpa [eligible] using h
    rw [Finset.prod_eq_zero (Multiset.mem_toFinset.mpr ha) (ite_eq_right ho)]
    simp [h, Nat.card_eq_fintype_card]

/-- Local factor for any positive part size `i`. -/
private noncomputable def factor (i : ℕ) : ℤ⟦X⟧ :=
  1 + ∑' j : ℕ, (2 : ℤ) • X ^ (i * (j + 1))

private lemma factor_mul_sub (i : ℕ) (hi : i ≠ 0) :
    factor i * (1 - X ^ i) = 1 + X ^ i := by
  let y := (X : ℤ⟦X⟧) ^ i
  have hy : constantCoeff y = 0 := by simp [y, hi]
  have hsum := WithPiTopology.summable_pow_of_constantCoeff_eq_zero hy
  have hgeom := WithPiTopology.tsum_pow_mul_one_sub_of_constantCoeff_eq_zero hy
  have h : factor i = 1 + (2 * y) * ∑' j : ℕ, y ^ j := by
    unfold factor
    rw [← hsum.tsum_mul_left]
    congr 1
    apply tsum_congr
    intro j
    simp [y, pow_mul, pow_succ', two_mul, add_mul]
  change factor i * (1 - y) = 1 + y
  rw [h]
  linear_combination 2 * y * hgeom

private lemma sub_ne (i : ℕ) (hi : i ≠ 0) : (1 : ℤ⟦X⟧) - X ^ i ≠ 0 := by
  intro h
  simpa [hi] using congrArg constantCoeff h

private lemma rescale_factor (i : ℕ) (hi : i ≠ 0) :
    (if Odd i then factor i else 1) * rescale (-1 : ℤ) (factor i) =
      if Odd i then 1 else factor i := by
  have h := congrArg (rescale (-1 : ℤ)) (factor_mul_sub i hi)
  simp only [map_mul, map_sub, map_add, map_one, map_pow, rescale_X, map_neg, neg_one_mul] at h
  by_cases ho : Odd i
  · simp only [ho, ite_true]
    rw [ho.neg_pow, sub_neg_eq_add, ← sub_eq_add_neg] at h
    apply mul_right_cancel₀ (b := 1 + X ^ i)
    · intro he
      simpa [hi] using congrArg constantCoeff he
    · rw [mul_assoc, h, factor_mul_sub i hi, one_mul]
  · have he := Nat.not_odd_iff_even.mp ho
    simp only [ho, ite_false, one_mul]
    rw [he.neg_pow] at h
    exact mul_right_cancel₀ (sub_ne i hi) (h.trans (factor_mul_sub i hi).symm)

private lemma expand_factor (i : ℕ) (hi : i ≠ 0) :
    expand 2 two_ne_zero (factor i) = factor (2 * i) := by
  have h := congrArg (expand 2 two_ne_zero (R := ℤ)) (factor_mul_sub i hi)
  simp only [map_mul, map_sub, map_pow, map_add, map_one, expand_X, ← pow_mul] at h
  have hn := mul_ne_zero two_ne_zero hi
  exact mul_right_cancel₀ (sub_ne _ hn) (h.trans (factor_mul_sub _ hn).symm)

/-- Multiplication by the twisted unrestricted series cancels each odd-part factor.
The remaining even-part factors give the unrestricted series at `X²`. -/
private lemma odd_mul_rescale_all :
    oddSeries * rescale (-1 : ℤ) allSeries = expand 2 two_ne_zero allSeries := by
  have hAll : HasProd (fun j => factor (j + 1)) allSeries :=
    Nat.Partition.hasProd_genFun _
  have hOdd : HasProd (fun j => if Odd (j + 1) then factor (j + 1) else 1) oddSeries := by
    apply (Nat.Partition.hasProd_genFun (fun i _ => if Odd i then (2 : ℤ) else 0)).congr_fun
    intro j
    by_cases h : Odd (j + 1) <;> simp [h, factor, PowerSeries.smul_eq_C_mul]
  have hR : Continuous (rescale (-1 : ℤ)) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    simp only [coeff_rescale]
    exact ((WithPiTopology.continuous_coeff ℤ n).const_mul _).tendsto F
  have hE : Continuous (expand 2 two_ne_zero (R := ℤ)) := by
    rw [continuous_iff_continuousAt]
    intro F
    rw [ContinuousAt, WithPiTopology.tendsto_iff_coeff_tendsto]
    intro n
    by_cases hd : 2 ∣ n
    · simpa [coeff_expand, hd] using (WithPiTopology.continuous_coeff ℤ (n / 2)).tendsto F
    · simp [coeff_expand, hd]
  let f (j : ℕ) : ℤ⟦X⟧ := if Odd (j + 1) then 1 else factor (j + 1)
  have hP : HasProd f (oddSeries * rescale (-1 : ℤ) allSeries) :=
    (hOdd.mul (hAll.map _ hR)).congr_fun fun j => (rescale_factor _ j.succ_ne_zero).symm
  have hEven : HasProd (fun j => f (2 * j)) 1 := by
    apply hasProd_one.congr_fun
    simp [f, parity_simps]
  have hOddIdx : HasProd (fun j => f (2 * j + 1)) (expand 2 two_ne_zero allSeries) := by
    apply (hAll.map _ hE).congr_fun
    intro j
    have he : Even (2 * j + 1 + 1) := ⟨j + 1, by ring⟩
    simp only [f, Nat.not_odd_iff_even.mpr he, ite_false, Function.comp_apply,
      expand_factor _ j.succ_ne_zero]
    congr 1
  simpa using hP.unique (hEven.even_mul_odd hOddIdx)

private noncomputable abbrev shiftedTheta :=
  expand 2 two_ne_zero (rescale (-1 : ℤ) squareThetaSeries)

/-- If `G` counts all overpartitions, then `θ(X) G(-X) = θ(-X²) G(X²) = 1`. -/
private lemma series_identity : shiftedTheta * oddSeries = squareThetaSeries := by
  have h : squareThetaSeries * rescale (-1 : ℤ) allSeries = 1 := theta_mul_rescale_genFun
  have hr := congrArg (rescale (-1 : ℤ)) h
  simp only [map_mul, rescale_rescale, neg_mul_neg, one_mul, rescale_one, RingHom.id_apply,
    map_one] at hr
  have he := congrArg (expand 2 two_ne_zero (R := ℤ)) hr
  rw [map_mul, map_one] at he
  calc
    shiftedTheta * oddSeries =
        (shiftedTheta * (oddSeries * rescale (-1 : ℤ) allSeries)) * squareThetaSeries := by
          linear_combination -(shiftedTheta * oddSeries) * h
    _ = squareThetaSeries := by rw [odd_mul_rescale_all, he, one_mul]

private lemma coeff_theta (n : ℕ) :
    squareThetaSeries.coeff n =
      if n = 0 then 1 else if n ∈ (Finset.Icc 1 n).image (fun m => m ^ 2) then 2 else 0 := by
  by_cases hn : n = 0
  · subst n
    simpa using coeff_squareThetaSeries_small.1
  rw [ite_eq_right hn, squareThetaSeries, coeff_mk]
  split_ifs with hs
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hm₁, hm₂⟩ := Finset.mem_Icc.mp hm
    have hset : ((Finset.Icc (-(↑(m ^ 2) : ℤ)) ↑(m ^ 2)).filter
        fun x : ℤ => x ^ 2 = ↑(m ^ 2)) = {(m : ℤ), -(m : ℤ)} := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_Icc, Nat.cast_pow, sq_eq_sq_iff_eq_or_eq_neg,
        Finset.mem_insert, Finset.mem_singleton]
      have hm' : (m : ℤ) ≤ (m : ℤ) ^ 2 := Int.le_self_sq _
      omega
    rw [hset]
    simp [show (m : ℤ) ≠ -(m : ℤ) by omega]
  · have hset : ((Finset.Icc (-(n : ℤ)) n).filter fun x : ℤ => x ^ 2 = n) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨_, hx⟩ := Finset.mem_filter.mp hx
      have he : x.natAbs ^ 2 = n := by exact_mod_cast (Int.natAbs_sq x).trans hx
      refine hs (Finset.mem_image.mpr ⟨x.natAbs, Finset.mem_Icc.mpr ⟨?_, ?_⟩, he⟩)
      · by_contra! hz
        simp [show x.natAbs = 0 by omega] at he
        omega
      · rw [← he]
        exact Nat.le_self_pow (by decide) _
    simp [hset]

private lemma shifted_at_square (k : ℕ) (hk : k ≠ 0) :
    shiftedTheta.coeff (2 * k ^ 2) = 2 * (-1 : ℤ) ^ k := by
  have hm : k ^ 2 ∈ (Finset.Icc 1 (k ^ 2)).image (fun m => m ^ 2) :=
    Finset.mem_image.mpr ⟨k, Finset.mem_Icc.mpr ⟨by omega, Nat.le_self_pow (by decide) _⟩, rfl⟩
  rw [coeff_expand_mul, coeff_rescale, coeff_theta, ite_eq_right (pow_ne_zero _ hk),
    ite_eq_left hm, mul_comm]
  congr 1
  apply neg_one_pow_congr
  simp [sq, parity_simps]

private lemma shifted_off_square (i : ℕ) (hi : i ≠ 0) (h : ∀ k : ℕ, 2 * k ^ 2 ≠ i) :
    shiftedTheta.coeff i = 0 := by
  by_cases hd : 2 ∣ i
  · obtain ⟨j, rfl⟩ := hd
    have hj : j ≠ 0 := by omega
    have hs : j ∉ (Finset.Icc 1 j).image (fun m => m ^ 2) := by
      rintro hm
      obtain ⟨m, _, rfl⟩ := Finset.mem_image.mp hm
      exact h m rfl
    rw [coeff_expand_mul, coeff_rescale, coeff_theta, ite_eq_right hj, ite_eq_right hs, mul_zero]
  · exact coeff_expand_of_not_dvd _ _ _ hd

end overpartitionOdd_square_recurrence

open overpartitionOdd_square_recurrence in
/-- **Square recurrence for overpartitions into odd parts.** Write $\mathrm{po}(m)$ for the
number of overpartitions of $m$ into odd parts. For every natural number $n$, the sum
$\mathrm{po}(n) + 2 \sum_{k \ge 1,\ 2k^2 \le n} (-1)^k \, \mathrm{po}(n - 2k^2)$ equals $1$ if
$n = 0$, equals $2$ if $n = m^2$ for some integer $m \ge 1$, and equals $0$ otherwise.

Source: Deepthi G. and S. Chandankumar, *Linear Relations for Overpartitions into Odd
Parts*, INTEGERS 26 (2026), Article A60, Theorem 5 (`integers-2026-A60-thm-5`). -/
public theorem overpartitionOdd_square_recurrence (n : ℕ) :
    (overpartitionOddPartsCount n : ℤ)
        + 2 * ∑ k ∈ (Finset.Icc 1 n).filter (fun k => 2 * k ^ 2 ≤ n),
          (-1 : ℤ) ^ k * (overpartitionOddPartsCount (n - 2 * k ^ 2) : ℤ)
      = if n = 0 then 1 else if n ∈ (Finset.Icc 1 n).image (fun m => m ^ 2) then 2 else 0 := by
  rw [← coeff_theta, ← series_identity, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  -- Only degree zero and twice the positive squares contribute to the convolution.
  let S := (Finset.Icc 1 n).filter fun k => 2 * k ^ 2 ≤ n
  let degrees := S.image (fun k => 2 * k ^ 2)
  have hsub : insert 0 degrees ⊆ Finset.range (n + 1) := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp
    · obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hi
      exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hk).2)
  have hzero : 0 ∉ degrees := by
    intro h
    obtain ⟨k, hk, he⟩ := Finset.mem_image.mp h
    have := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
    simp_all
  have hinj : Set.InjOn (fun k : ℕ => 2 * k ^ 2) S := by
    intro a _ b _ hab
    change 2 * a ^ 2 = 2 * b ^ 2 at hab
    exact Nat.pow_left_injective (by decide : 2 ≠ 0) (Nat.eq_of_mul_eq_mul_left (by decide) hab)
  rw [← Finset.sum_subset hsub fun i hi hiS => by
    have hi₀ : i ≠ 0 := fun h => hiS (h ▸ Finset.mem_insert_self ..)
    have hmiss (k : ℕ) (hk : 2 * k ^ 2 = i) : False := by
      have hk₀ : k ≠ 0 := by rintro rfl; simp_all
      have hki := Nat.le_self_pow (by decide : 2 ≠ 0) k
      have hin := Finset.mem_range.mp hi
      apply hiS (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨k, ?_, hk⟩))
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, by omega⟩
    rw [shifted_off_square i hi₀ hmiss, zero_mul]]
  have h₀ : shiftedTheta.coeff 0 = 1 := by
    simpa [shiftedTheta, PowerSeries.coeff_expand, PowerSeries.coeff_rescale] using
      coeff_squareThetaSeries_small.1
  rw [Finset.sum_insert hzero, h₀, one_mul, Nat.sub_zero, coeff_oddSeries,
    Finset.sum_image hinj, Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk₁ := (Finset.mem_Icc.mp (Finset.mem_filter.mp hk).1).1
  rw [shifted_at_square k (by omega), coeff_oddSeries, mul_assoc]

end MetaMathlibExt
