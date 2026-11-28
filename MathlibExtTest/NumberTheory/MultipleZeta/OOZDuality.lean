/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.NumberTheory.MultipleZeta.OOZDuality

open MetaMathlibExt

example : szDualIndex [2, 0, 1] = [1, 2, 0] := by decide

example : szQMZV (szBlockIndex []) = 1 :=
  (szQMZV_szBlockIndex_dual [] (by simp)).trans szQMZV_nil

-- A block with no zero entries is dual to an index starting with 1.
example : szQMZV [3] = szQMZV [1, 0, 0] :=
  szQMZV_szBlockIndex_dual [(3, 1)] (by simp)

-- Both reversing the block order and swapping the two entries matter here.
example : szQMZV [2, 0, 0, 1, 0] = szQMZV [2, 3, 0] :=
  szQMZV_szBlockIndex_dual [(2, 3), (1, 2)] (by simp)

example : oozToSZ [3, 2] [2, 1] = 4 := by
  have h : Finset.Icc 1 3 = {1, 2, 3} := by decide
  norm_num [oozToSZ, oozToSZTail, h, Finset.sum_range_succ, Finsupp.mapDomain_add,
    Finsupp.single_apply, Nat.choose]

-- The preimage of the dual of [1, 0] under V has a negative coefficient.
example : oozQMZV [2] - oozQMZV [1] = oozQMZV [1, 0] := by
  let x : List ℕ →₀ ℚ := Finsupp.single [2] 1 - Finsupp.single [1] 1
  have hx : x ∈ Finsupp.supported ℚ ℚ {v : List ℕ | ∀ a ∈ v.head?, 1 ≤ a} := by
    apply Submodule.sub_mem
    · exact Finsupp.single_mem_supported ℚ _ (by simp)
    · exact Finsupp.single_mem_supported ℚ _ (by simp)
  have hV : Finsupp.linearCombination ℚ oozToSZ x = (oozToSZ [1, 0]).mapDomain szDualIndex := by
    have h : Finset.Icc 1 2 = {1, 2} := by decide
    simp [x, oozToSZ, oozToSZTail, h, Nat.choose, szDualIndex, szWord, szIndexOfWordAux]
  have h := sum_oozQMZV_eq_of_oozToSZ_eq_szDual [1, 0] (by simp) x hx hV
  change Finsupp.linearCombination ℚ oozQMZV x = _ at h
  simpa [x] using h

open Finset PowerSeries

private def partitionFour (i : Fin 5) : Nat.Partition 4 :=
  let parts : Fin 5 → Multiset ℕ := ![{4}, {3, 1}, {2, 2}, {2, 1, 1}, {1, 1, 1, 1}]
  have h : ∀ j, (parts j).sum = 4 := by decide
  Nat.Partition.ofSums 4 (parts i) (h i)

private lemma card_partition_four : Fintype.card (Nat.Partition 4) = 5 := by
  let sizes := Icc 1 4
  let weights := (sizes.finsuppAntidiag 4).filter fun w => ∀ i ∈ sizes, i ∣ w i
  have hw : weights.card = 5 := by decide
  have mem_weights (p : Nat.Partition 4) : p.toFinsuppAntidiag ∈ weights := by
    refine mem_filter.mpr ⟨p.toFinsuppAntidiag_mem_finsuppAntidiag, fun i _ => ?_⟩
    exact ⟨p.parts.count i, Nat.mul_comm _ _⟩
  apply Nat.le_antisymm
  · have h := Fintype.card_le_of_injective
      (fun p => (⟨p.toFinsuppAntidiag, mem_weights p⟩ : weights))
      (fun _ _ h => Nat.Partition.toFinsuppAntidiag_injective 4 (congrArg Subtype.val h))
    simpa only [Fintype.card_coe, hw] using h
  · have hinj : ∀ i j, partitionFour i = partitionFour j → i = j := by decide
    simpa only [Fintype.card_fin] using Fintype.card_le_of_injective partitionFour hinj

example : (∑ r ∈ Icc 1 4, coeff 4 (szQMZV (List.replicate r 1))) = 5 := by
  rw [sum_coeff_szQMZV_replicate_one_eq_card_partition (hN := by decide) (hR := by decide),
    card_partition_four]
  norm_num

-- Raising the cutoff does not change the coefficient.
example : (∑ r ∈ Icc 1 6, coeff 4 (szQMZV (List.replicate r 1))) = 5 := by
  rw [sum_coeff_szQMZV_replicate_one_eq_card_partition (hN := by decide) (hR := by decide),
    card_partition_four]
  norm_num

-- Compute the inverse coefficients independently, using (1 - q^m) times its inverse.
private lemma coeff_inv_one_sub_pow_of_pos {m : ℕ} (hm : 0 < m) (a : ℕ) :
    coeff a ((1 - X ^ m : ℚ⟦X⟧)⁻¹) = if m ∣ a then 1 else 0 := by
  induction a using Nat.strong_induction_on with
  | ind a ih =>
    have hu := PowerSeries.mul_inv_cancel (1 - (X : ℚ⟦X⟧) ^ m) (by simp [hm.ne'])
    have hc := congrArg (fun p : ℚ⟦X⟧ => coeff a p) hu
    simp only [sub_mul, one_mul, map_sub, coeff_X_pow_mul', coeff_one] at hc
    obtain rfl | ha := Nat.eq_zero_or_pos a
    · simpa [hm.not_ge] using hc
    · rw [ite_eq_right (Nat.ne_of_gt ha)] at hc
      by_cases hma : m ≤ a
      · rw [ite_eq_left hma, sub_eq_zero, ih (a - m) (by omega)] at hc
        have hd : m ∣ a - m ↔ m ∣ a := by
          constructor
          · intro h
            simpa only [Nat.sub_add_cancel hma] using Nat.dvd_add h (dvd_refl m)
          · exact fun h => Nat.dvd_sub h (dvd_refl m)
        simpa only [hd] using hc
      · rw [ite_eq_right hma, sub_zero] at hc
        rwa [ite_eq_right (fun h => hma (Nat.le_of_dvd ha h))]

private lemma coeff_weight_mul (a b n : ℕ) :
    coeff n ((X ^ a * (1 - X ^ a)⁻¹) * (X ^ b * (1 - X ^ b)⁻¹) : ℚ⟦X⟧) =
      if a + b ≤ n then
        ∑ j ∈ range (n - (a + b) + 1),
          coeff j ((1 - X ^ a : ℚ⟦X⟧)⁻¹) * coeff (n - (a + b) - j) ((1 - X ^ b : ℚ⟦X⟧)⁻¹)
      else 0 := by
  have he : (X ^ a * (1 - X ^ a)⁻¹) * (X ^ b * (1 - X ^ b)⁻¹) = X ^ (a + b) *
      (((1 - X ^ a : ℚ⟦X⟧)⁻¹) * (1 - X ^ b)⁻¹) := by
    rw [pow_add]
    ac_rfl
  rw [he, coeff_X_pow_mul', coeff_mul, Nat.sum_antidiagonal_eq_sum_range_succ_mk]

example : coeff 0 (szQMZV []) = 1 ∧ coeff 1 (szQMZV []) = 0 := by
  simp [szQMZV_nil, coeff_one]

example : coeff 0 (szQMZV [2, 0]) = 0 := by
  rw [coeff_szQMZV_eq_coeff_partial, szQMZVPartial_cons, show Ioo 0 1 = ∅ by decide]
  simp

-- The nonzero terms at q^6 have first sizes 2 and 3. Their contributions are 2 and 2.
example : coeff 6 (szQMZV [2, 0]) = 4 := by
  have hzero (M : ℕ) : szQMZVPartial [0] M = ((M - 1 : ℕ) : ℚ⟦X⟧) := by
    simp [szQMZVPartial_cons, szQMZVPartial_nil]
  rw [coeff_szQMZV_eq_coeff_partial, szQMZVPartial_cons, ← Ico_add_one_left_eq_Ioo,
    sum_Ico_eq_sum_range, map_sum]
  simp only [hzero, coeff_mul_natCast, pow_two, coeff_weight_mul]
  norm_num [sum_range_succ, coeff_inv_one_sub_pow_of_pos]

-- In the interior gap there is one choice for a chain 3 > a > 1 and two for 4 > a > 1.
example : coeff 5 (szQMZV [1, 0, 1]) = 3 := by
  simp only [coeff_szQMZV_eq_coeff_partial, szQMZVPartial_cons, szQMZVPartial_nil,
    pow_zero, pow_one, one_mul, mul_one, ← Ico_add_one_left_eq_Ioo, zero_add,
    sum_Ico_eq_sum_range, mul_sum, map_sum, coeff_weight_mul]
  norm_num only [sum_range_succ, sum_range_zero, sum_empty, coeff_inv_one_sub_pow_of_pos,
    Nat.dvd_zero, add_zero, zero_add, zero_mul, mul_zero, one_mul, mul_one]
  norm_num

-- Compute the same coefficient through the public formula, checking the interior gap.
example : coeff 5 (szQMZV [1, 0, 1]) = 3 := by
  let k : Fin 2 → ℕ := fun _ => 1
  let d : Fin 2 → ℕ := ![2, 1]
  have hindex : szBlockIndex (List.ofFn fun j => (k j, d j)) = [1, 0, 1] := by decide
  rw [← hindex, coeff_szQMZV_szBlockIndex_eq_sum_choose 2 k d (by decide) (by decide) 5]
  decide +kernel

-- The exported theorem is available without importing the old wanted module.
example (N : ℕ) :
    coeff N (szQMZV (szBlockIndex [(2, 2)])) =
      ∑ mn ∈ (Fintype.piFinset fun _ : Fin 1 => range (N + 1)) ×ˢ
          (Fintype.piFinset fun _ : Fin 1 => range (N + 1)) with
          StrictAnti mn.1 ∧ (∀ j, 0 < mn.1 j) ∧ (∀ j, 0 < mn.2 j) ∧
            ∑ j, mn.1 j * mn.2 j = N,
        ∏ j : Fin 1, ((mn.2 j - 1).choose 1 : ℚ) *
          ((mn.1 j - (if h : j.val + 1 < 1 then mn.1 ⟨j.val + 1, h⟩ else 0) - 1).choose 1 : ℚ) := by
  simpa only [Nat.cast_mul, List.ofFn_succ, List.ofFn_zero, show (2 : ℕ) - 1 = 1 by decide] using
    coeff_szQMZV_szBlockIndex_eq_sum_choose 1 (fun _ => 2) (fun _ => 2)
      (fun _ => by decide) (fun _ => by decide) N
