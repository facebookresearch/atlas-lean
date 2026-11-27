/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.ZeckendorfNewInformationZone
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic.IntervalCases

open MetaMathlibExt

namespace ZeckendorfNewInformationZoneTest

/-- Adding the digit `x (m + 2)` on top of the prefix value of order `m`. -/
private theorem prefixValue_succ (m : ℕ) (x : ℕ → Bool) :
    zeckAdicPrefixValue (m + 1) x =
      zeckAdicPrefixValue m x + if x (m + 2) = true then Nat.fib (m + 2) else 0 :=
  Finset.sum_Icc_succ_top (by omega) _

/-- The prefix value of order `0` is the empty sum. -/
private theorem prefixValue_zero (x : ℕ → Bool) : zeckAdicPrefixValue 0 x = 0 := by
  simp [zeckAdicPrefixValue]

/-- The constant sequence `0` is a Zeckendorf-adic integer. -/
private theorem zero_mem_zeckAdic : (fun _ : ℕ => false) ∈ zeckAdic :=
  ⟨rfl, rfl, fun _ => Or.inl rfl⟩

-- The prefix value of order `4` of the block `x₅x₄x₃x₂ = 1010` is `F₅ + F₃ = 7`.
example : zeckAdicPrefixValue 4 (fun i => decide (i = 3 ∨ i = 5)) = 7 := by decide

-- `NIZ₀` is empty because `0 - 1` is read as `0`.
example (r : ℕ) : zeckNIZ r 0 = ∅ := by simp [zeckNIZ]

-- For the shift `r = 1`, the point whose only digit `1` is `x₃` (prefix value `F₃ = 2`) lies in
-- `NIZ₄`: `2 + 1 < F₅ = 5`, while `2 + 1 ≥ F₄ = 3` and `2 < F₄` keep it out of `CST₃`.
example : (fun i => decide (i = 3)) ∈ zeckNIZ 1 4 := by
  simp only [zeckNIZ, zeckCST, Set.mem_sdiff, Set.mem_ofPred_eq]
  decide

-- The same point does not lie in `NIZ₃`, since it is not in `CST₃`.
example : (fun i => decide (i = 3)) ∉ zeckNIZ 1 3 := by
  simp only [zeckNIZ, zeckCST, Set.mem_sdiff, Set.mem_ofPred_eq]
  decide

/-- For the shift `r = 1`, the cylinder `C₀₀` of order `2` lies in `NIZ₂`. -/
private theorem cylinder_00_subset :
    zeckAdic ∩ {x | x (2 + 1) = false ∧ x 2 = false ∧
      ∀ i, 2 ≤ i → i ≤ 2 - 1 → x i = (fun _ : ℕ => false) i} ⊆ zeckNIZ 1 2 := by
  rintro x ⟨-, h3, h2, -⟩
  have v1 : zeckAdicPrefixValue 1 x = 0 := by
    rw [prefixValue_succ, prefixValue_zero]
    simp [h2]
  have v2 : zeckAdicPrefixValue 2 x = 0 := by
    rw [prefixValue_succ, v1]
    simp [h3]
  simp only [zeckNIZ, zeckCST, Set.mem_sdiff, Set.mem_ofPred_eq, v1, v2]
  decide

-- For the shift `r = 1`, two applications of the theorem starting from `C₀₀ ⊆ NIZ₂` give
-- `C₀₀₁₀ ⊆ NIZ₄` and then `C₀₀₁₀₁₀ ⊆ NIZ₆`.
example {x : ℕ → Bool} (hx : x ∈ zeckAdic) (h7 : x 7 = false) (h6 : x 6 = false)
    (h5 : x 5 = true) (h4 : x 4 = false) (h3 : x 3 = true) (h2 : x 2 = false) :
    x ∈ zeckNIZ 1 6 := by
  have step := zeckNIZ_cylinder_shift (r := 1) (k := 2) le_rfl le_rfl zero_mem_zeckAdic
    cylinder_00_subset
  let y : ℕ → Bool := fun i => decide (i = 3)
  have hy : y ∈ zeckAdic := by
    refine ⟨rfl, rfl, fun i => ?_⟩
    simp only [y, decide_eq_false_iff_not]
    omega
  have hC : zeckAdic ∩ {x | x (4 + 1) = false ∧ x 4 = false ∧
      ∀ i, 2 ≤ i → i ≤ 4 - 1 → x i = y i} ⊆ zeckNIZ 1 4 := by
    rintro z ⟨hz, hz5, hz4, hzy⟩
    exact step ⟨hz, hz5, hz4, hzy 3 (by omega) (by omega), hzy 2 (by omega) (by omega),
      fun i hi hi' => by omega⟩
  refine zeckNIZ_cylinder_shift (r := 1) (k := 4) le_rfl (by omega) hy hC
    ⟨hx, h7, h6, h5, h4, fun i hi hi' => ?_⟩
  interval_cases i
  · exact h2
  · exact h3

-- For the shift `r = 2`, the cylinder `C₀₀₀` of order `3` lies in `NIZ₃` (it is the bottom
-- level `v₃ = 0` of the large tower, and `0 + 2 < F₄ = 3`), so the cylinder `C₀₀₁₀₀` of order
-- `5` lies in `NIZ₅`.
example {x : ℕ → Bool} (hx : x ∈ zeckAdic) (h6 : x 6 = false) (h5 : x 5 = false)
    (h4 : x 4 = true) (h3 : x 3 = false) (h2 : x 2 = false) : x ∈ zeckNIZ 2 5 := by
  have hC : zeckAdic ∩ {x | x (3 + 1) = false ∧ x 3 = false ∧
      ∀ i, 2 ≤ i → i ≤ 3 - 1 → x i = (fun _ : ℕ => false) i} ⊆ zeckNIZ 2 3 := by
    rintro z ⟨-, hz4, hz3, hzy⟩
    have v1 : zeckAdicPrefixValue 1 z = 0 := by
      rw [prefixValue_succ, prefixValue_zero]
      simp [hzy 2 le_rfl (by omega)]
    have v2 : zeckAdicPrefixValue 2 z = 0 := by
      rw [prefixValue_succ, v1]
      simp [hz3]
    have v3 : zeckAdicPrefixValue 3 z = 0 := by
      rw [prefixValue_succ, v2]
      simp [hz4]
    simp only [zeckNIZ, zeckCST, Set.mem_sdiff, Set.mem_ofPred_eq, v2, v3]
    decide
  refine zeckNIZ_cylinder_shift (r := 2) (k := 3) (by omega) (by omega) zero_mem_zeckAdic hC
    ⟨hx, h6, h5, h4, h3, fun i hi hi' => ?_⟩
  interval_cases i
  exact h2

/-- A sequence whose only digit `1` sits at an index `n ≥ 2` is a Zeckendorf-adic integer. -/
private theorem single_mem_zeckAdic {n : ℕ} (hn : 2 ≤ n) :
    (fun i => decide (i = n)) ∈ zeckAdic :=
  ⟨decide_eq_false_iff_not.2 (by omega), decide_eq_false_iff_not.2 (by omega),
    fun i => by simp only [decide_eq_false_iff_not]; omega⟩

-- The hypotheses of `zeckNIZ_leading_zeros` are satisfiable: for the shift `r = 1` the point
-- whose only digit `1` is `x₃` lies in `NIZ₄`, and the name `x₅x₄x₃x₂ = 0010` of its cylinder of
-- order `4` starts with `00`.
example : (fun i => decide (i = 3)) 5 = false ∧ (fun i => decide (i = 3)) 4 = false :=
  zeckNIZ_leading_zeros (r := 1) (k := 4) le_rfl (by omega) (single_mem_zeckAdic (by omega))
    (by simp only [zeckNIZ, zeckCST, Set.mem_sdiff, Set.mem_ofPred_eq]; decide)

-- In set form: the Zeckendorf-adic points of `NIZ_k` lie in the cylinder `x_{k+1} = x_k = 0`.
example {r k : ℕ} (hr : 1 ≤ r) (hk : 2 ≤ k) :
    zeckAdic ∩ zeckNIZ r k ⊆ {x | x (k + 1) = false ∧ x k = false} :=
  fun _ hx => zeckNIZ_leading_zeros hr hk hx.1 hx.2

-- Whatever the shift `r ≥ 1`, a point whose digit `x₄` is `1` does not lie in `NIZ₄`.
example {r : ℕ} (hr : 1 ≤ r) : (fun i => decide (i = 4)) ∉ zeckNIZ r 4 := fun h =>
  absurd (zeckNIZ_leading_zeros hr (by omega) (single_mem_zeckAdic (by omega)) h).2 (by decide)

-- Whatever the shift `r ≥ 1`, a point whose digit `x₅` is `1` does not lie in `NIZ₄`.
example {r : ℕ} (hr : 1 ≤ r) : (fun i => decide (i = 5)) ∉ zeckNIZ r 4 := fun h =>
  absurd (zeckNIZ_leading_zeros hr (by omega) (single_mem_zeckAdic (by omega)) h).1 (by decide)

-- The point with digits `x₅ = x₃ = 1` lies neither in `NIZ₄` (its digit `x₅` is `1`) nor in
-- `NIZ₅` (its digit `x₅` is `1` again, now in the second leading position), for any `r ≥ 1`.
example {r : ℕ} (hr : 1 ≤ r) :
    (fun i => decide (i = 3 ∨ i = 5)) ∉ zeckNIZ r 4 ∧
      (fun i => decide (i = 3 ∨ i = 5)) ∉ zeckNIZ r 5 := by
  have hx : (fun i => decide (i = 3 ∨ i = 5)) ∈ zeckAdic :=
    ⟨by decide, by decide, fun i => by simp only [decide_eq_false_iff_not]; omega⟩
  exact ⟨fun h => absurd (zeckNIZ_leading_zeros hr (by omega) hx h).1 (by decide),
    fun h => absurd (zeckNIZ_leading_zeros hr (by omega) hx h).2 (by decide)⟩

/-- The Zeckendorf digit sequence of `1 = F₂` has its only digit `1` at index `2`. -/
private theorem zeckAdicOfNat_one : zeckAdicOfNat 1 = fun i => decide (i = 2) := by
  have h : Nat.zeckendorf 1 = [2] :=
    Nat.zeckendorf_sum_fib (l := [2]) (by unfold List.IsZeckendorfRep; decide)
  funext i
  simp only [zeckAdicOfNat, h, List.mem_singleton]

-- On the digit sequences of natural numbers the odometer is addition: two steps from `i(2)`, the
-- point with the single digit `x₃ = 1`, reach `i(4)`, whose digits `x₄ = x₂ = 1` give `F₄ + F₂`.
example : zeckOdometer^[2] (zeckAdicOfNat 2) = fun i => decide (i = 2 ∨ i = 4) := by
  have h : Nat.zeckendorf 4 = [4, 2] :=
    Nat.zeckendorf_sum_fib (l := [4, 2]) (by unfold List.IsZeckendorfRep; decide)
  rw [zeckOdometer_iterate_zeckAdicOfNat]
  funext i
  simp only [zeckAdicOfNat, show 2 + 2 = 4 from rfl, h, List.mem_cons, List.not_mem_nil,
    or_false]
  by_cases hi : i = 2 <;> simp [hi, or_comm]

-- The variation `Δ^{(1)}` at the zero sequence is `s(1) - s(0) = 1`: every truncated variation of
-- order `k ≥ 2` counts the new digit `x₂ = 1`.
example : zeckAdicVariation 1 (fun _ => false) = 1 := by
  apply zeckAdicVariation_eq_of_eventually
  refine Filter.eventually_atTop.2 ⟨2, fun k hk => ?_⟩
  have h0 : (fun _ : ℕ => false) = zeckAdicOfNat 0 := by
    funext i
    simp [zeckAdicOfNat]
  rw [zeckAdicTruncVariation, h0, zeckOdometer_iterate_zeckAdicOfNat, Nat.zero_add,
    zeckAdicOfNat_one]
  have h : ∀ i ∈ Finset.Icc 2 k, (((decide (i = 2)).toNat : ℕ) : ℤ) = if i = 2 then 1 else 0 :=
    fun i _ => by by_cases hi : i = 2 <;> simp [hi]
  simp only [Finset.sum_congr rfl h, Finset.sum_ite_eq', Finset.mem_Icc, le_refl, hk, and_self,
    ite_true]
  simp

-- For `ℓ = 3`, the shift is `F₃ = 2`: among the `v < F₆ = 8` whose digit sequence lies in `NIZ₄`
-- (these are `v = 1, 2`), the variation is `0` once and `1` once.
example :
    {v | v < 8 ∧ zeckAdicOfNat v ∈ zeckNIZ 2 4 ∧
        zeckAdicVariation 2 (zeckAdicOfNat v) = 0}.ncard = 1 ∧
      {v | v < 8 ∧ zeckAdicOfNat v ∈ zeckNIZ 2 4 ∧
        zeckAdicVariation 2 (zeckAdicOfNat v) = 1}.ncard = 1 :=
  zeckNIZ_fib_variation_order_succ (ℓ := 3) le_rfl

-- For `ℓ = 5`, the shift is `F₅ = 5`: among the `v < F₈ = 21` whose digit sequence lies in
-- `NIZ₆`, the variation is `0` for `F₄ = 3` of them and `1` for `F₃ = 2` of them.
example :
    {v | v < 21 ∧ zeckAdicOfNat v ∈ zeckNIZ 5 6 ∧
        zeckAdicVariation 5 (zeckAdicOfNat v) = 0}.ncard = 3 ∧
      {v | v < 21 ∧ zeckAdicOfNat v ∈ zeckNIZ 5 6 ∧
        zeckAdicVariation 5 (zeckAdicOfNat v) = 1}.ncard = 2 :=
  zeckNIZ_fib_variation_order_succ (ℓ := 5) (by omega)

-- Together the two counts give `F_{ℓ-1} + F_{ℓ-2} = F_ℓ` levels of `NIZ_{ℓ+1}` below `F_{ℓ+3}`.
example {ℓ : ℕ} (hℓ : 3 ≤ ℓ) :
    {v | v < Nat.fib (ℓ + 3) ∧ zeckAdicOfNat v ∈ zeckNIZ (Nat.fib ℓ) (ℓ + 1) ∧
        zeckAdicVariation (Nat.fib ℓ) (zeckAdicOfNat v) = 0}.ncard +
      {v | v < Nat.fib (ℓ + 3) ∧ zeckAdicOfNat v ∈ zeckNIZ (Nat.fib ℓ) (ℓ + 1) ∧
        zeckAdicVariation (Nat.fib ℓ) (zeckAdicOfNat v) = 1}.ncard = Nat.fib ℓ := by
  obtain ⟨h0, h1⟩ := zeckNIZ_fib_variation_order_succ hℓ
  obtain ⟨n, rfl⟩ : ∃ n, ℓ = n + 2 := ⟨ℓ - 2, by omega⟩
  rw [h0, h1, show n + 2 - 1 = n + 1 by omega, show n + 2 - 2 = n by omega, Nat.fib_add_two,
    Nat.add_comm]

end ZeckendorfNewInformationZoneTest
