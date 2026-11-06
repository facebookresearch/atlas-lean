/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechNormSixPairPointStabilizer

/-! Actual simultaneous point stabilizers for every norm-four and paired norm-six lattice flag. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The genuine Conway simultaneous point stabilizer of an ordered integral lattice flag. -/
def leechNormSixActualPairStabilizer (x y : leechIntegral) : Subgroup leechIsomSubgroup :=
  MulAction.stabilizer leechIsomSubgroup (x, y)

/-- The actual flag stabilizer fixes both original integral vectors pointwise. -/
theorem leechNormSixActualPairStabilizer_mem (x y : leechIntegral) (g : leechIsomSubgroup) :
    g ∈ leechNormSixActualPairStabilizer x y ↔
      leechIntegralAction g x = x ∧ leechIntegralAction g y = y := by
  change (leechIntegralAction g x, leechIntegralAction g y) = (x, y) ↔ _
  constructor
  · intro h
    exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩
  · rintro ⟨hx, hy⟩
    rw [hx, hy]

/-- The complete standard flag stabilizer is the original subgroup identified by the actual
953856-vector transitivity proof. -/
theorem leechNormSixActualPairStabilizer_standard (u : LeechNormSixPair) :
    leechNormSixActualPairStabilizer leechRootedA2Root u.val =
      leechNormSixPairPointStabilizer u := by
  ext g
  rw [leechNormSixActualPairStabilizer_mem, leechNormSixPairPointStabilizer_mem]

/-- Every actual norm-four vector has a genuine Conway transporter to the positive standard root. -/
theorem leechNormSixActualPair_root_transport (x : leechIntegral)
    (hx : leechSquareSum x.val = 32) :
    ∃ a : leechIsomSubgroup, leechIntegralAction a x = leechRootedA2Root := by
  obtain ⟨a, _, ha⟩ := leechShort_concrete_transitive x hx
  refine ⟨a, Subtype.ext ?_⟩
  rw [ha]
  funext i
  by_cases hi0 : i = 0
  · subst i
    norm_num [leechShortPairTarget, leechRootedA2Root, leechRootedA2RootIntegral]
  · by_cases hi1 : i = 1
    · subst i
      norm_num [leechShortPairTarget, leechRootedA2Root, leechRootedA2RootIntegral]
    · simp [leechShortPairTarget, leechRootedA2Root, leechRootedA2RootIntegral, hi0, hi1]

/-- Every genuine norm-four and paired norm-six flag has exactly44352000 point stabilizers
in the original Conway group, without a model-recognition or transitivity hypothesis. -/
theorem leechNormSixActualPairStabilizer_card (x y : leechIntegral)
    (hx : leechSquareSum x.val = 32) (hy : leechSquareSum y.val = 48)
    (hp : leechIntegralPairing x.val y.val = 16) :
    Nat.card (leechNormSixActualPairStabilizer x y) = 44352000 := by
  obtain ⟨a, ha⟩ := leechNormSixActualPair_root_transport x hx
  have hay : leechSquareSum (leechIntegralAction a y).val = 48 := by
    rw [leechIntegralAction_squareSum, hy]
  have hap : (leechIntegralAction a y).val 0 + (leechIntegralAction a y).val 1 = 4 := by
    have h := leechRootedA2_integral_pairing_action a x y
    rw [ha, hp] at h
    change leechIntegralPairing leechRootedA2RootIntegral _ = 16 at h
    rw [leechRootedA2RootIntegral_pairing] at h
    omega
  let u : LeechNormSixPair := ⟨leechIntegralAction a y, hay, hap⟩
  have hpair : a • (x, y) = (leechRootedA2Root, u.val) := by
    change (leechIntegralAction a x, leechIntegralAction a y) = _
    rw [ha]
  have h := Nat.card_congr (MulAction.stabilizerEquivStabilizer hpair.symm).toEquiv
  change Nat.card (leechNormSixActualPairStabilizer x y) =
    Nat.card (leechNormSixActualPairStabilizer leechRootedA2Root u.val) at h
  rw [h, leechNormSixActualPairStabilizer_standard, leechNormSixPairPointStabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
