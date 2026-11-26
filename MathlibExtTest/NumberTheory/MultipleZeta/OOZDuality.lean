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
