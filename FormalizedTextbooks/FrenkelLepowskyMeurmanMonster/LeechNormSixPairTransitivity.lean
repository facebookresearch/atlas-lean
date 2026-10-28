/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairXiReduction
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairOddThreeTransitivity

/-! Actual transitivity on the complete 953856-vector paired norm-six catalogue. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- Every actual paired norm-six vector reaches the original odd three-coordinate family under
the genuine positive-root stabilizer. -/
theorem leechNormSixPair_reduction (u : LeechNormSixPair) :
    ∃ e : leechRootedA2PositiveRootSubgroup,
      leechNormEightMultiplicity (e • u).val.val = leechNormSixShapeCounts 3 := by
  obtain ⟨s, hs⟩ := leechNormSix_catalog u.val u.property.1
  fin_cases s
  · exact leechNormSixPair_even_xi_reduction u 0 hs (Or.inl rfl)
  · exact leechNormSixPair_even_xi_reduction u 1 hs (Or.inr rfl)
  · exact leechNormSixPair_odd_five_xi_reduction u hs
  · exact ⟨1, by simpa [leechNormSixShapeCounts] using hs⟩

/-- The full genuine positive-root stabilizer is transitive on every actual norm-six vector
paired two with its fixed norm-four root. -/
theorem leechNormSixPair_transitive (u v : LeechNormSixPair) :
    ∃ e : leechRootedA2PositiveRootSubgroup, e • u = v := by
  obtain ⟨a, ha⟩ := leechNormSixPair_reduction u
  obtain ⟨b, hb⟩ := leechNormSixPair_reduction v
  obtain ⟨c, hc⟩ := leechNormSixPair_odd_three_transitive (a • u) (b • v) ha hb
  refine ⟨b⁻¹ * c * a, ?_⟩
  rw [mul_smul, mul_smul, hc, inv_smul_smul]

/-- Each genuine paired-vector orbit covers the complete original actual catalogue. -/
theorem leechNormSixPair_orbit (u : LeechNormSixPair) :
    MulAction.orbit leechRootedA2PositiveRootSubgroup u = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro v
  exact leechNormSixPair_transitive u v

/-- The actual paired-vector orbit has precisely the verified catalogue cardinality. -/
theorem leechNormSixPair_orbit_card (u : LeechNormSixPair) :
    Nat.card (MulAction.orbit leechRootedA2PositiveRootSubgroup u) = 953856 := by
  rw [leechNormSixPair_orbit, Nat.card_univ, leechNormSixPair_card]

/-- Every actual norm-six vector in this genuine root orbit has a stabilizer of order44352000. -/
theorem leechNormSixPair_stabilizer_card (u : LeechNormSixPair) :
    Nat.card (MulAction.stabilizer leechRootedA2PositiveRootSubgroup u) = 44352000 := by
  have h := Nat.card_congr
    (MulAction.orbitProdStabilizerEquivGroup leechRootedA2PositiveRootSubgroup u)
  rw [Nat.card_prod, leechNormSixPair_orbit_card, leechRootedA2PositiveRootSubgroup_card] at h
  omega

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
