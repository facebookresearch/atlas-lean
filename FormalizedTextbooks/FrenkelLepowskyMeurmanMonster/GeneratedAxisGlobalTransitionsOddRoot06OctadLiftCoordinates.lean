/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSupportBindings
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTransitionsOddRoot06OctadSparseBindings

/-! Every actual lift of the genuine standard frame carries the complete original sparse support to unit octad coefficients. -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-- Every actual lift has the same proved preferred-short permutation of the complete support. -/
theorem generatedAxisGlobalOddRoot06OctadLift_supported_square
    (x : GriessSpace) (f : localFiberSubgroup)
    (hf : f.val.2 = generatedAxisGlobalOddRoot06OctadStandardFrameIsometry)
    (hs : ∀ r, (griessConwayEncode x).2.1 r =
      (generatedAxisGlobalOddRoot06OctadSparseShortQ r : ℝ))
    (r : GriessShortIndex) (hr : generatedOctadShortSupport generatedOctadBasisOctad r) :
    (griessConwayEncode (localGriessRepresentation f x)).2.1 r ^ 2 = 1 := by
  obtain ⟨p, rfl⟩ := generatedAxisGlobalOddRoot06OctadTarget_coverage r hr
  have hp : griessShortPermutation f.val.2 (generatedAxisGlobalOddRoot06OctadSourceLabel p) =
      generatedAxisGlobalOddRoot06OctadTargetLabel p := by
    rw [hf]
    exact generatedAxisGlobalOddRoot06OctadShortPermutation_frame p
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply, ← hp]
  change (localShortOperator f (griessConwayEncode x).2.1
    (griessShortPermutation f.val.2 (generatedAxisGlobalOddRoot06OctadSourceLabel p))) ^ 2 = 1
  rw [localShortOperator_image, hs, generatedAxisGlobalOddRoot06OctadSparseShortQ_source,
    mul_pow, pow_two, qSign_sq, one_mul]
  exact_mod_cast generatedAxisGlobalOddRoot06OctadSourceCoefficient_unit p

/-- An actual lift creates no coordinate outside the fully covered original octad support. -/
theorem generatedAxisGlobalOddRoot06OctadLift_unsupported_zero
    (x : GriessSpace) (f : localFiberSubgroup)
    (hf : f.val.2 = generatedAxisGlobalOddRoot06OctadStandardFrameIsometry)
    (hs : ∀ r, (griessConwayEncode x).2.1 r =
      (generatedAxisGlobalOddRoot06OctadSparseShortQ r : ℝ))
    (r : GriessShortIndex) (hr : ¬ generatedOctadShortSupport generatedOctadBasisOctad r) :
    (griessConwayEncode (localGriessRepresentation f x)).2.1 r = 0 := by
  obtain ⟨s, rfl⟩ := (griessShortPermutation f.val.2).surjective r
  have hz : generatedAxisGlobalOddRoot06OctadSparseShortQ s = 0 := by
    have hn : generatedAxisGlobalOddRoot06OctadSparseSource s = none := by
      cases h : generatedAxisGlobalOddRoot06OctadSparseSource s with
      | none => rfl
      | some p =>
        have hp := generatedAxisGlobalOddRoot06OctadSparse_sound s p h
        subst s
        have hperm : griessShortPermutation f.val.2
            (generatedAxisGlobalOddRoot06OctadSourceLabel p) =
              generatedAxisGlobalOddRoot06OctadTargetLabel p := by
          rw [hf]
          exact generatedAxisGlobalOddRoot06OctadShortPermutation_frame p
        rw [hperm] at hr
        exact False.elim (hr (generatedAxisGlobalOddRoot06OctadTarget_supported p))
    simp only [generatedAxisGlobalOddRoot06OctadSparseShortQ, hn]
  rw [localGriessRepresentation_encode, localConwayRawRepresentation_apply]
  change localShortOperator f _ (griessShortPermutation f.val.2 s) = 0
  rw [localShortOperator_image, hs, hz, Rat.cast_zero, mul_zero]

end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
