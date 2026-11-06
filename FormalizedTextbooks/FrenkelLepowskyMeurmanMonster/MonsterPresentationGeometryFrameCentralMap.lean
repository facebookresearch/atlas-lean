/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- Faithful projection of the original source-local central subgroup onto the actual Q center. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFrameQuotient

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option backward.isDefEq.respectTransparency false

/-- The actual Q projection maps every source-local central generator power into actual centerQ. -/
def monsterGeometryFrameCentralIntoQCenter : monsterGeometryFrameSourceZ →* centerQ where
  toFun x := ⟨monsterGeometryFrameIntoQ x.val, by
    rw [← qQuotHom_ker]
    exact monsterGeometryFrameSourceZ_le_binary_ker x.property⟩
  map_one' := Subtype.ext (map_one monsterGeometryFrameIntoQ)
  map_mul' x y := Subtype.ext (map_mul monsterGeometryFrameIntoQ x.val y.val)

/-- Every actual extraspecial central element is the image of a genuine source-local z power. -/
theorem monsterGeometryFrameCentralIntoQCenter_surjective :
    Function.Surjective monsterGeometryFrameCentralIntoQCenter := by
  intro q
  by_cases he : q.val = 1
  · refine ⟨1, ?_⟩
    apply Subtype.ext
    exact (map_one monsterGeometryFrameIntoQ).trans he.symm
  · have hz := qCentralInvolution_eq_of_mem_center_ne_one q.val q.property he
    refine ⟨⟨monsterGeometryFrameSourceCentral, Subgroup.mem_zpowers _⟩, ?_⟩
    apply Subtype.ext
    exact monsterGeometryFrameIntoQ_central.trans hz.symm

/-- Faithfulness on the source-local central subgroup follows from its proved exact two elements. -/
theorem monsterGeometryFrameCentralIntoQCenter_bijective :
    Function.Bijective monsterGeometryFrameCentralIntoQCenter := by
  have : Finite monsterGeometryFrameSourceZ := Nat.finite_of_card_ne_zero
    (by rw [monsterGeometryFrameSourceZ_card]; decide)
  apply monsterGeometryFrameCentralIntoQCenter_surjective.bijective_of_nat_card_le
  rw [monsterGeometryFrameSourceZ_card, centerQ_card]

/-- Actual isomorphism of the original source-local central subgroup with the existing Q center. -/
def monsterGeometryFrameCentralEquiv : monsterGeometryFrameSourceZ ≃* centerQ :=
  MulEquiv.ofBijective monsterGeometryFrameCentralIntoQCenter
    monsterGeometryFrameCentralIntoQCenter_bijective

/-- The natural Q projection is faithful on elements of the original source-local z subgroup. -/
theorem monsterGeometryFrameIntoQ_injective_on_central
    (x y : monsterGeometryFrameLocalSubgroup)
    (hx : x ∈ monsterGeometryFrameSourceZ) (hy : y ∈ monsterGeometryFrameSourceZ)
    (h : monsterGeometryFrameIntoQ x = monsterGeometryFrameIntoQ y) : x = y := by
  have he : monsterGeometryFrameCentralIntoQCenter ⟨x, hx⟩ =
      monsterGeometryFrameCentralIntoQCenter ⟨y, hy⟩ := Subtype.ext h
  exact congrArg Subtype.val (monsterGeometryFrameCentralIntoQCenter_bijective.injective he)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
