/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The natural source-local homomorphism onto the actual extraspecial group. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFrameImage

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- The literal natural Monster map, restricted to the verified local source subgroup and
corestricted to the genuine extraspecial image. -/
def monsterGeometryFrameIntoQRange : monsterGeometryFrameLocalSubgroup →* qIntoGenerated.range where
  toFun x := ⟨monsterGeometryIntoGenerated x.val,
    monsterGeometryFrame_local_image_le_Q (Subgroup.mem_map_of_mem _ x.property)⟩
  map_one' := Subtype.ext (map_one monsterGeometryIntoGenerated)
  map_mul' x y := Subtype.ext (map_mul monsterGeometryIntoGenerated x.val y.val)

/-- Actual Q-valued source-local projection; the inverse is the proved faithful actual inclusion. -/
def monsterGeometryFrameIntoQ : monsterGeometryFrameLocalSubgroup →* Q :=
  (MonoidHom.ofInjective qIntoGenerated_injective).symm.toMonoidHom.comp
    monsterGeometryFrameIntoQRange

/-- Projection retains the literal natural Monster map on every source-local element. -/
theorem monsterGeometryFrameIntoQ_generated (x : monsterGeometryFrameLocalSubgroup) :
    qIntoGenerated (monsterGeometryFrameIntoQ x) = monsterGeometryIntoGenerated x.val :=
  MonoidHom.apply_ofInjective_symm qIntoGenerated_injective (monsterGeometryFrameIntoQRange x)

/-- The independent source-local subgroup maps onto the actual extraspecial group. -/
theorem monsterGeometryFrameIntoQ_surjective : Function.Surjective monsterGeometryFrameIntoQ := by
  intro q
  have hm : qIntoGenerated q ∈ monsterGeometryFrameLocalImage := by
    rw [monsterGeometryFrame_local_image_eq_Q]
    exact ⟨q, rfl⟩
  obtain ⟨x, hx, he⟩ := hm
  refine ⟨⟨x, hx⟩, ?_⟩
  apply qIntoGenerated_injective
  rw [monsterGeometryFrameIntoQ_generated]
  exact he

/-- The distinguished original generator as an element of the verified local source subgroup. -/
def monsterGeometryFrameSourceCentral : monsterGeometryFrameLocalSubgroup :=
  ⟨PresentedGroup.of monsterGeometryBasePoint, monsterGeometryFrame_local_base_mem⟩

/-- The source-local distinguished generator maps to the literal actual central involution. -/
theorem monsterGeometryFrameIntoQ_central :
    monsterGeometryFrameIntoQ monsterGeometryFrameSourceCentral = qCentralInvolution := by
  apply qIntoGenerated_injective
  rw [monsterGeometryFrameIntoQ_generated]
  exact monsterGeometryIntoGenerated_generator monsterGeometryBasePoint

/-- Literal phase lifts retain their full Q values under the source-local projection. -/
theorem monsterGeometryFrameIntoQ_point (p : MonsterCo1GeometryPoint) (q : Q)
    (hq : toAdd (qQuotHom q) = p.val) :
    monsterGeometryFrameIntoQ
      ⟨PresentedGroup.of (monsterGeometryFrameLiftPoint p q hq),
        monsterGeometryFrame_local_point_mem p q hq⟩ = q := by
  apply qIntoGenerated_injective
  rw [monsterGeometryFrameIntoQ_generated]
  exact monsterGeometryIntoGenerated_generator (monsterGeometryFrameLiftPoint p q hq)

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
