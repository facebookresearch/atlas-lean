/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairCount
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairCountTotalData

/-! Exact cardinality of the actual norm-six vectors paired with the standard norm-four root. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

/-- Exactly 953856 actual norm-six lattice vectors have coordinate sum four at the fixed pair. -/
theorem leechNormSixPair_card : Nat.card LeechNormSixPair = 953856 := by
  let _ := Fintype.ofFinite golayCode
  rw [← Nat.card_congr leechNormSixPairSourceEquiv]
  change Nat.card (Σ m : Bool, Σ c : golayCode, LeechNormSixPairBoundedSolution m c) = _
  rw [Nat.card_sigma]
  simp_rw [Nat.card_sigma, leechNormSixPairBoundedSolution_card]
  rw [Fintype.sum_bool, ← Finset.sum_add_distrib]
  rw [← Equiv.sum_comp golayCodeLabelEquiv]
  simp_rw [leechNormSixPairExpectedContribution_label]
  calc
    _ = ∑ d : Fin 4096, leechNormSixPairLabelContribution d := by
      apply Finset.sum_congr rfl
      intro d _
      exact Nat.add_comm _ _
    _ = 953856 := leechNormSixPairLabelContribution_sum

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
