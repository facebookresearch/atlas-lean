/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisClassificationOctadSupportAction

/-! Coordinate facts for the genuine local images of triality octad axes. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
open scoped Matrix
set_option backward.isDefEq.respectTransparency false

/-- A section-preserving local element retains unit signs on all supported labels. -/
theorem generatedOctad_local_image_supported_square
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (f : localFiberSubgroup)
    (hg : generatedOctadPreserves (golayOctadWord o) f.val.2)
    (r : GriessShortIndex) (hr : generatedOctadShortSupport o r) :
    (griessConwayEncode (localGriessRepresentation f
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)))).2.1 r ^ 2 = 1 := by
  obtain ⟨s, rfl⟩ := (griessShortPermutation f.val.2).surjective r
  have hs := (generatedOctadShortSupport_permutation_iff o f.val.2 hg s).mp hr
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change (localShortOperator f _ (griessShortPermutation f.val.2 s)) ^ 2 = 1
  rw [localShortOperator_image, mul_pow,
    generatedAxis_triality_octad_supported_square o e c s hs, mul_one, pow_two, qSign_sq]

/-- A section-preserving local element creates no short coordinate outside the support. -/
theorem generatedOctad_local_image_unsupported_zero
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (f : localFiberSubgroup)
    (hg : generatedOctadPreserves (golayOctadWord o) f.val.2)
    (r : GriessShortIndex) (hr : ¬ generatedOctadShortSupport o r) :
    (griessConwayEncode (localGriessRepresentation f
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)))).2.1 r = 0 := by
  obtain ⟨s, rfl⟩ := (griessShortPermutation f.val.2).surjective r
  have hs := mt (generatedOctadShortSupport_permutation_iff o f.val.2 hg s).mpr hr
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localShortOperator f _ (griessShortPermutation f.val.2 s) = 0
  rw [localShortOperator_image, generatedAxis_triality_octad_unsupported_zero o e c s hs,
    mul_zero]

/-- Every local image of a triality octad axis still has zero tensor coordinates. -/
theorem generatedOctad_local_image_tensor_zero
    (o : Fin 759) (e : Fin 64) (c : ZMod 2) (f : localFiberSubgroup) :
    (griessConwayEncode (localGriessRepresentation f
      (sExtra (conwayShortAxis (Sum.inr (Sum.inl (o, e))) c)))).2.2 = 0 := by
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localTensorRepresentation f _ = 0
  rw [generatedAxis_triality_octad_tensor_zero_all, map_zero]

/-- Any genuine scaled Griess idempotent satisfies the required raw short-coordinate equation. -/
theorem generatedAxis_raw_idempotent_short (x : GriessSpace)
    (hx : griessProd x x = (64 : ℝ) • x) (r : GriessShortIndex) :
    (conwayRawProduct (griessConwayEncode x) (griessConwayEncode x)).2.1 r =
      64 * (griessConwayEncode x).2.1 r := by
  have he := congrArg (fun y => (griessConwayEncode y).2.1 r) hx
  rw [griessProd_encode] at he
  have hs := griessConwayEncodeLinear.map_smul 64 x
  change griessConwayEncode ((64 : ℝ) • x) = (64 : ℝ) • griessConwayEncode x at hs
  rw [hs] at he
  exact he

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
