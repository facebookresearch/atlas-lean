/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/- The genuine frame-generated source subgroup maps onto the actual extraspecial subgroup. -/
module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.MonsterPresentationGeometryFrameLocal
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedCo1GeometryPointSpan

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open Multiplicative
set_option backward.isDefEq.respectTransparency false

/-- Actual image of the explicitly frame-generated independent source subgroup. -/
def monsterGeometryFrameLocalImage : Subgroup G :=
  monsterGeometryFrameLocalSubgroup.map monsterGeometryIntoGenerated

/-- Every original frame generator has its actual value inside the genuine extraspecial group. -/
theorem monsterGeometryFrame_local_image_le_Q :
    monsterGeometryFrameLocalImage ≤ qIntoGenerated.range := by
  apply Subgroup.map_le_iff_le_comap.mpr
  apply (Subgroup.closure_le _).mpr
  intro x hx
  change monsterGeometryIntoGenerated x ∈ qIntoGenerated.range
  rcases hx with hx | ⟨p, q, hq, rfl⟩
  · have he : x = PresentedGroup.of monsterGeometryBasePoint := hx
    rw [he, monsterGeometryIntoGenerated_generator]
    exact ⟨qCentralInvolution, rfl⟩
  · rw [monsterGeometryIntoGenerated_generator]
    exact ⟨q, rfl⟩

/-- The actual image of the explicit source subgroup contains the genuine central involution. -/
theorem monsterGeometryFrame_local_image_central :
    qCentralInvolution ∈ monsterGeometryFrameLocalImage.comap qIntoGenerated := by
  refine ⟨PresentedGroup.of monsterGeometryBasePoint, monsterGeometryFrame_local_base_mem, ?_⟩
  exact monsterGeometryIntoGenerated_generator monsterGeometryBasePoint

/-- Actual Conway frame spanning makes the binary image of the source local subgroup full. -/
theorem monsterGeometryFrame_local_image_binary :
    qSubgroupBinaryImage (monsterGeometryFrameLocalImage.comap qIntoGenerated) = ⊤ := by
  apply top_unique
  have hspan : Submodule.span (ZMod 2) generatedCo1GeometryPoints = ⊤ :=
    generatedCo1GeometryPointSpan_eq_top
  rw [← hspan]
  apply Submodule.span_le.mpr
  intro v hv
  let p : MonsterCo1GeometryPoint := ⟨v, hv⟩
  let q : Q := ⟨ofAdd v, 1⟩
  have hq : toAdd (qQuotHom q) = p.val := rfl
  refine ⟨q, ?_, rfl⟩
  refine ⟨PresentedGroup.of (monsterGeometryFrameLiftPoint p q hq),
    monsterGeometryFrame_local_point_mem p q hq, ?_⟩
  exact monsterGeometryIntoGenerated_generator (monsterGeometryFrameLiftPoint p q hq)

/-- The natural source map has exactly the genuine extraspecial group as its local image.
Its kernel on this subgroup remains a separate recognition obligation. -/
theorem monsterGeometryFrame_local_image_eq_Q :
    monsterGeometryFrameLocalImage = qIntoGenerated.range := by
  apply le_antisymm monsterGeometryFrame_local_image_le_Q
  have he := qSubgroup_eq_top_of_binaryImage_eq_top
    (monsterGeometryFrameLocalImage.comap qIntoGenerated)
    (centerQ_le_of_central_mem _ monsterGeometryFrame_local_image_central)
    monsterGeometryFrame_local_image_binary
  rintro x ⟨q, rfl⟩
  have hq : q ∈ monsterGeometryFrameLocalImage.comap qIntoGenerated := by
    rw [he]
    exact Subgroup.mem_top q
  exact hq

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
