/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.Additive.RestrictedSignedSumsetAPEquality

open MetaMathlibExt

private def progression {k : ℕ} (b d : ℤ) (i : Fin k) : ℤ := b + (i.val : ℤ) * d

private theorem progression_strictMono {k : ℕ} (b : ℤ) {d : ℤ} (hd : 0 < d) :
    StrictMono (progression (k := k) b d) := by
  intro i j hij
  have h : (i.val : ℤ) < (j.val : ℤ) := by exact_mod_cast (show i.val < j.val from hij)
  exact add_lt_add_of_le_of_lt le_rfl (Int.mul_lt_mul_of_pos_right h hd)

private theorem progression_isIndexedAP {k : ℕ} (b : ℤ) {d : ℤ} (hd : 0 < d) :
    IsIndexedAP (progression (k := k) b d) d := by
  refine ⟨hd, fun i j hij => ?_⟩
  have h : (j.val : ℤ) = (i.val : ℤ) + 1 := by exact_mod_cast hij.symm
  simp only [progression, h, add_mul, one_mul, add_assoc]

-- Odd h and the shortest possible progression.
example : ((restrictedSignedSumset 3 (orderedFinset (progression (k := 4) 1 2))).card : ℤ) = 16 := by
  exact (card_restrictedSignedSumset_ap_ge 3 4 (by decide) (by decide) _ 2
    (progression_strictMono 1 (by decide)) (by decide)
    (progression_isIndexedAP 1 (by decide))).2.mpr (by decide)

-- Equality for an even number of summands, on a longer progression scaled by two.
example : ((restrictedSignedSumset 4 (orderedFinset (progression (k := 7) 2 4))).card : ℤ) = 41 := by
  exact (card_restrictedSignedSumset_ap_ge 4 7 (by decide) (by decide) _ 4
    (progression_strictMono 2 (by decide)) (by decide)
    (progression_isIndexedAP 2 (by decide))).2.mpr (by decide)

-- A nonextremal step gives the stronger lower bound and rules out the smaller cardinality.
example :
    let c : ℤ := (restrictedSignedSumset 3 (orderedFinset (progression (k := 6) 2 3))).card
    29 ≤ c ∧ c ≠ 28 := by
  obtain ⟨hbound, heq⟩ := card_restrictedSignedSumset_ap_ge 3 6 (by decide) (by decide) _ 3
    (progression_strictMono 2 (by decide)) (by decide) (progression_isIndexedAP 2 (by decide))
  have hne : (3 : ℤ) ≠ 2 * progression (k := 6) 2 3 0 := by decide
  change _ ≥ (if (3 : ℤ) = 2 * progression (k := 6) 2 3 0 then _ else _) at hbound
  rw [ite_eq_right hne] at hbound
  exact ⟨hbound, fun hc => hne (heq.mp hc)⟩
