/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.LeechRootedA2PlaneTransitivity
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisE8ShortFlagStabilizer

/-! The actual stabilizer of the standard short-root line in the genuine Conway group. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The original preferred label of the standard root4(e0+e1). -/
def leechRootedA2RootAddress : GriessShortIndex :=
  Sum.inl (1, griessCoordinatePairEquiv.symm ⟨(0, 1), by decide +kernel⟩)

/-- The original preferred root label represents the actual standard root. -/
theorem leechRootedA2RootAddress_integral :
    griessShortLatticeVector leechRootedA2RootAddress = leechRootedA2Root := by
  have hp : griessCoordinatePair
      (griessCoordinatePairEquiv.symm ⟨(0, 1), by decide +kernel⟩) = (0, 1) :=
    congrArg Subtype.val (griessCoordinatePairEquiv.apply_symm_apply _)
  apply Subtype.ext
  funext i
  change griessShortIntegral leechRootedA2RootAddress i = leechRootedA2RootIntegral i
  simp only [leechRootedA2RootAddress, griessShortIntegral,
    hp, leechRootedA2RootIntegral]
  norm_num

/-- Equality of actual short labels is exactly signed equality of the integral images. -/
theorem leechRootedA2_short_perm_eq_iff (e : leechIsomSubgroup) (r s : GriessShortIndex) :
    griessShortPermutation e r = s ↔
      leechIntegralAction e (griessShortLatticeVector r) = griessShortLatticeVector s ∨
      leechIntegralAction e (griessShortLatticeVector r) = -griessShortLatticeVector s := by
  constructor
  · intro h
    simpa only [h] using leechRootedA2_short_integral_image e r
  · intro h
    rcases leechRootedA2_short_integral_image e r with hi | hi
    · rcases h with h | h
      · exact griessShort_label_unique _ _ (Or.inl (congrArg Subtype.val (hi.symm.trans h)))
      · exact griessShort_label_unique _ _ (Or.inr (congrArg Subtype.val (hi.symm.trans h)))
    · rcases h with h | h
      · apply griessShort_label_unique _ _
        right
        have hn := congrArg Neg.neg (hi.symm.trans h)
        exact congrArg Subtype.val (by simpa only [neg_neg] using hn)
      · exact griessShort_label_unique _ _
          (Or.inl (congrArg Subtype.val (neg_injective (hi.symm.trans h))))

/-- The genuine Conway stabilizer of the standard short-root line. -/
def leechRootedA2RootLineSubgroup : Subgroup leechIsomSubgroup :=
  MulAction.stabilizer leechIsomSubgroup leechRootedA2RootAddress

/-- Actual subgroup membership fixes the genuine root with either of its lattice signs. -/
theorem leechRootedA2RootLineSubgroup_mem (e : leechIsomSubgroup) :
    e ∈ leechRootedA2RootLineSubgroup ↔ leechRootedA2PreservesRootLine e := by
  change griessShortPermutation e leechRootedA2RootAddress = leechRootedA2RootAddress ↔ _
  rw [leechRootedA2_short_perm_eq_iff, leechRootedA2RootAddress_integral]
  rfl

/-- Actual short-label transitivity makes the standard-root orbit the entire original catalogue. -/
theorem leechRootedA2RootAddress_orbit :
    MulAction.orbit leechIsomSubgroup leechRootedA2RootAddress = Set.univ := by
  apply Set.eq_univ_iff_forall.mpr
  intro r
  obtain ⟨e, _, he⟩ := leechShort_concrete_label_transitive leechRootedA2RootAddress r
  exact ⟨e, he⟩

/-- The genuine standard-root orbit has precisely98280 original short labels. -/
theorem leechRootedA2RootAddress_orbit_card :
    Nat.card (MulAction.orbit leechIsomSubgroup leechRootedA2RootAddress) = 98280 := by
  rw [leechRootedA2RootAddress_orbit, Nat.card_univ, Nat.card_eq_fintype_card,
    griessShortIndex_card]

/-- The full actual Conway root-line stabilizer has84610842624000 elements. -/
theorem leechRootedA2RootLineSubgroup_card :
    Nat.card leechRootedA2RootLineSubgroup = 84610842624000 := by
  let : Finite leechIsomSubgroup := leechIsomSubgroup_finite
  let _ := Fintype.ofFinite leechIsomSubgroup
  let _ := Fintype.ofFinite (MulAction.orbit leechIsomSubgroup leechRootedA2RootAddress)
  let _ := Fintype.ofFinite leechRootedA2RootLineSubgroup
  have h := MulAction.card_orbit_mul_card_stabilizer_eq_card_group
    leechIsomSubgroup leechRootedA2RootAddress
  simp only [← Nat.card_eq_fintype_card] at h
  change Nat.card (MulAction.orbit leechIsomSubgroup leechRootedA2RootAddress) *
    Nat.card leechRootedA2RootLineSubgroup = Nat.card leechIsomSubgroup at h
  rw [leechRootedA2RootAddress_orbit_card, co0_card_exact] at h
  exact Nat.eq_of_mul_eq_mul_left (by decide : 0 < 98280)
    (h.trans (by decide : 8315553613086720000 = 98280 * 84610842624000))

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
