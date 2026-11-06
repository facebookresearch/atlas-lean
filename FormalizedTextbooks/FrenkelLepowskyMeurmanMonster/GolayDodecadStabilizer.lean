/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayDodecadOrbit
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GolayDodecadAction

/-! Exact order of the actual dodecad and outside-point stabilizer. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual point stabilizer covers every genuine dodecad outside coordinate zero. -/
theorem golayDodecadOutsideZero_orbit :
    MulAction.orbit (golayPointStabilizer 1) (golayDodecadOrbitCodeLabel 0) =
      ↑(golayDodecadsOutside 0) := by
  ext d
  rw [MulAction.mem_orbit_iff]
  constructor
  · rintro ⟨p, rfl⟩
    change golayLabelPermutation p.val (golayDodecadOrbitCodeLabel 0) ∈
      golayDodecadsOutside 0
    have hp := (golayPointStabilizer_one_iff p.val).mp p.property
    have hm := (golayLabelPermutation_dodecad_outside p.val
      (golayDodecadOrbitCodeLabel 0) 0).mpr (golayDodecadOrbitCodeLabel_mem 0)
    rwa [hp] at hm
  · intro hd
    obtain ⟨p, hp0, hp⟩ := golayDodecadsOutside_zero_reaches d hd
    have he : golayLabelPermutation p (golayDodecadOrbitCodeLabel 0) = d := by
      apply golayLabelCoefficients_injective
      apply golayEncoder_injective
      rw [golayLabelPermutation_word]
      exact hp
    exact ⟨⟨p, (golayPointStabilizer_one_iff p).mpr hp0⟩, he⟩

/-- The genuine point-stabilizer orbit has exactly 1288 elements. -/
theorem golayDodecadOutsideZero_orbit_card :
    Nat.card (MulAction.orbit (golayPointStabilizer 1) (golayDodecadOrbitCodeLabel 0)) =
      1288 := by
  rw [golayDodecadOutsideZero_orbit, Nat.card_eq_fintype_card]
  change Fintype.card (golayDodecadsOutside 0) = 1288
  rw [Fintype.card_coe, golayDodecadsOutside_zero_card]

/-- Inside the actual coordinate-zero stabilizer, the actual dodecad stabilizer has order 7920. -/
theorem golayDodecadOutsideZero_stabilizer_card :
    Nat.card (MulAction.stabilizer (golayPointStabilizer 1)
      (golayDodecadOrbitCodeLabel 0)) = 7920 := by
  have h := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup
    (golayPointStabilizer 1) (golayDodecadOrbitCodeLabel 0))
  rw [Nat.card_prod, golayDodecadOutsideZero_orbit_card,
    golayPointStabilizer_one_card] at h
  omega

/-- The actual simultaneous stabilizer viewed in the original full automorphism group. -/
def golayDodecadOutsideZeroStabilizer : Subgroup golayAutomorphismSubgroup :=
  (MulAction.stabilizer (golayPointStabilizer 1) (golayDodecadOrbitCodeLabel 0)).map
    (golayPointStabilizer 1).subtype

/-- The genuine simultaneous stabilizer in the full Golay automorphism group has order 7920. -/
theorem golayDodecadOutsideZeroStabilizer_card :
    Nat.card golayDodecadOutsideZeroStabilizer = 7920 := by
  rw [golayDodecadOutsideZeroStabilizer, Subgroup.card_subtype,
    golayDodecadOutsideZero_stabilizer_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
