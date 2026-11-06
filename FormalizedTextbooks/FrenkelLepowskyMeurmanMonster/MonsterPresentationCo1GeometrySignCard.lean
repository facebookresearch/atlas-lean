/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Counting the actual Conway sign subgroup by its two genuine central real lifts. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationCo1GeometryBaseStabilizer

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster

/-- The all-one published Golay generator as a genuine codeword. -/
def monsterCo1GeometryAllOneCode : golayCode :=
  ⟨fun _ => 1, by
    have h := golayGenerator_mem 11
    simpa only [golayGeneratorBit_all_one, Int.cast_one] using h⟩

/-- Its actual sign map is literally the negative identity of the real Leech space. -/
theorem monsterCo1GeometryAllOne_negative :
    golaySignHom (Multiplicative.ofAdd monsterCo1GeometryAllOneCode) =
      leechNegativeIdentity := by
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  ext i
  change qSign 1 * x i = -x i
  rw [qSign_one, neg_one_mul]

/-- The actual codeword class homomorphism is the quotient of its genuine real sign map. -/
theorem monsterCo1GeometrySignClass_value (d : Multiplicative golayCode) :
    monsterCo1GeometrySignClassHom d =
      (QuotientGroup.mk' signsSubgroup) (golaySignHom d) := rfl

/-- Kernel codewords correspond to the two genuine central real signs. -/
def monsterCo1GeometrySignKernelIntoSigns :
    monsterCo1GeometrySignClassHom.ker →* signsSubgroup where
  toFun d := ⟨golaySignHom d.val, by
    have hd : monsterCo1GeometrySignClassHom d.val = 1 := d.property
    rw [monsterCo1GeometrySignClass_value] at hd
    exact (QuotientGroup.eq_one_iff (golaySignHom d.val)).mp hd⟩
  map_one' := Subtype.ext golaySignHom.map_one
  map_mul' d e := Subtype.ext (golaySignHom.map_mul d.val e.val)

/-- Distinct kernel codewords give distinct actual real signs. -/
theorem monsterCo1GeometrySignKernelIntoSigns_injective :
    Function.Injective monsterCo1GeometrySignKernelIntoSigns := by
  intro d e h
  apply Subtype.ext
  exact golaySignHom_injective (congrArg Subtype.val h)

/-- Both central real signs have actual Golay codeword preimages in this kernel. -/
theorem monsterCo1GeometrySignKernelIntoSigns_surjective :
    Function.Surjective monsterCo1GeometrySignKernelIntoSigns := by
  intro s
  rcases s.property with hs | hs
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    change golaySignHom 1 = s.val
    rw [map_one]
    exact (Subtype.ext hs).symm
  · have hk : Multiplicative.ofAdd monsterCo1GeometryAllOneCode ∈
        monsterCo1GeometrySignClassHom.ker := by
      change monsterCo1GeometrySignClassHom _ = 1
      rw [monsterCo1GeometrySignClass_value, monsterCo1GeometryAllOne_negative]
      exact (QuotientGroup.eq_one_iff leechNegativeIdentity).mpr (Or.inr (fun _ => rfl))
    refine ⟨⟨Multiplicative.ofAdd monsterCo1GeometryAllOneCode, hk⟩, ?_⟩
    apply Subtype.ext
    change golaySignHom (Multiplicative.ofAdd monsterCo1GeometryAllOneCode) = s.val
    rw [monsterCo1GeometryAllOne_negative]
    apply Subtype.ext
    apply LinearEquiv.ext
    intro x
    exact (hs x).symm

/-- The actual codeword-class kernel has exactly two elements. -/
theorem monsterCo1GeometrySignClass_kernel_card :
    Nat.card monsterCo1GeometrySignClassHom.ker = 2 := by
  rw [Nat.card_congr (Equiv.ofBijective monsterCo1GeometrySignKernelIntoSigns
    ⟨monsterCo1GeometrySignKernelIntoSigns_injective,
      monsterCo1GeometrySignKernelIntoSigns_surjective⟩)]
  exact signsSubgroup_card

/-- The genuine codeword-sign image inside actual Conway has exactly 2¹¹ elements. -/
theorem monsterCo1GeometrySignClass_range_card :
    Nat.card monsterCo1GeometrySignClassHom.range = 2048 := by
  have h := monsterCo1GeometrySignClassHom.ker.card_mul_index
  rw [monsterCo1GeometrySignClass_kernel_card, Subgroup.index_eq_card,
    Nat.card_congr (QuotientGroup.quotientKerEquivRange monsterCo1GeometrySignClassHom).toEquiv,
    Nat.card_congr Multiplicative.toAdd, golayCode_card] at h
  omega

/-- The intrinsic two-core of the full actual norm-eight base-point stabilizer has order 2¹¹. -/
theorem monsterCo1GeometryBasePoint_twoCore_card :
    Nat.card (monsterCo1GeometryPointTwoCore monsterCo1GeometryBasePoint) = 2048 := by
  rw [monsterCo1GeometryBasePoint_twoCore, monsterCo1GeometrySignClass_range_card]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
