/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairCountData

/-! Counting actual paired norm-six vectors through their unique original source parameters. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

instance (m : Bool) (a b : ZMod 2) : Fintype (LeechNormSixPairPrefixChoice m a b) := by
  unfold LeechNormSixPairPrefixChoice
  infer_instance

/-- The remaining binary codeword has at most 22 nonzero coordinates. -/
theorem leechNormSixTail_weight_le (c : Fin 22 → ZMod 2) : ∑ i, (c i).val ≤ 22 := by
  calc
    (∑ i, (c i).val) ≤ ∑ _ : Fin 22, 1 := by
      apply Finset.sum_le_sum
      intro i _
      have h := ZMod.val_lt (c i)
      omega
    _ = 22 := by simp

/-- The exact coefficient table counts every actual remaining source assignment. -/
theorem leechNormSixTailSolution_card (m : Bool) (c : Fin 22 → ZMod 2)
    (q : ℕ) (hq : q < 65) (h : ZMod 8) :
    Nat.card (LeechNormSixTailSolution m c q h) =
      leechNormSixTailCount m (∑ i, (c i).val) q h := by
  have hw : (∑ i, (c i).val) < 23 := by have := leechNormSixTail_weight_le c; omega
  rw [← leechNormSixTailSeries_count, leechNormSixTailSeries_weight]
  rw [leechNormSixPair_tail_table m ⟨∑ i, (c i).val, hw⟩ ⟨q, hq⟩ h]
  unfold leechNormSixTailCount
  rw [dite_eq_left hw, dite_eq_left hq]

/-- The first two original bits and the remaining bits recover the entire original Golay weight. -/
theorem leechNormSixPair_weight_split (c : golayCode) :
    (c.val 0).val + (c.val 1).val +
      (∑ i : Fin 22, (c.val i.succ.succ).val) = ∑ i : Fin 24, (c.val i).val := by
  conv_rhs => rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  rw [show (0 : Fin 23).succ = (1 : Fin 24) by decide]
  omega

/-- Counting the exact prefix and every remaining coordinate gives the finite
source contribution. -/
theorem leechNormSixPairBoundedSolution_contribution (m : Bool) (c : golayCode) :
    Nat.card (LeechNormSixPairBoundedSolution m c) =
      leechNormSixPairContribution m (∑ i, (c.val i).val) (c.val 0) (c.val 1) := by
  have hsplit := leechNormSixPair_weight_split c
  have htail : (∑ i : Fin 22, (c.val i.succ.succ).val) =
      (∑ i : Fin 24, (c.val i).val) - (c.val 0).val - (c.val 1).val := by omega
  calc
    Nat.card (LeechNormSixPairBoundedSolution m c) =
        ∑ p : LeechNormSixPairPrefixChoice m (c.val 0) (c.val 1),
          Nat.card (LeechNormSixTailSolution m (fun i => c.val i.succ.succ)
            (48 - leechNormSixPairPrefixSquare p.val) (4 * (m.toNat : ZMod 8) - 4)) := by
      rw [← Nat.card_congr (leechNormSixPairPartsEquiv m c)]
      exact Nat.card_sigma
    _ = ∑ p : LeechNormSixPairPrefixChoice m (c.val 0) (c.val 1),
        leechNormSixTailCount m (∑ i : Fin 22, (c.val i.succ.succ).val)
          (48 - leechNormSixPairPrefixSquare p.val) (4 * (m.toNat : ZMod 8) - 4) := by
      apply Finset.sum_congr rfl
      intro p _
      exact leechNormSixTailSolution_card m _ _ (by omega) _
    _ = _ := by
      unfold leechNormSixPairContribution
      rw [← leechNormSixPairBoundedPrefix_catalogue]
      simp_rw [htail]
      exact Finset.sum_coe_sort
        (f := fun p => leechNormSixTailCount m
          ((∑ i, (c.val i).val) - (c.val 0).val - (c.val 1).val)
          (48 - leechNormSixPairPrefixSquare p) (4 * (m.toNat : ZMod 8) - 4))
        (s := leechNormSixPairBoundedPrefix m (c.val 0) (c.val 1))

/-- Every actual Golay source fiber has the evaluated contribution, without count assumptions. -/
theorem leechNormSixPairBoundedSolution_card (m : Bool) (c : golayCode) :
    Nat.card (LeechNormSixPairBoundedSolution m c) =
      leechNormSixPairExpectedContribution m (∑ i, (c.val i).val) (c.val 0) (c.val 1) := by
  rw [leechNormSixPairBoundedSolution_contribution]
  have hw := golayCode_weights c.val c.property
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  have hlt : (∑ i, (c.val i).val) < 25 := by
    rcases hw with h | h | h | h | h <;> omega
  have hsplit := leechNormSixPair_weight_split c
  have ht := leechNormSixTail_weight_le (fun i => c.val i.succ.succ)
  have hb0 : (c.val 0).val + (c.val 1).val ≤ ∑ i, (c.val i).val := by omega
  have hb1 : (∑ i, (c.val i).val) ≤ 22 + (c.val 0).val + (c.val 1).val := by omega
  exact leechNormSixPairContribution_expected m ⟨∑ i, (c.val i).val, hlt⟩
    (c.val 0) (c.val 1) hw hb0 hb1

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
