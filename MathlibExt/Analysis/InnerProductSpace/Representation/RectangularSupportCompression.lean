/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import MathlibExt.Analysis.InnerProductSpace.Representation.SupportCompression
public import Mathlib.Analysis.Normed.Operator.Compact.Basic

/-!
# Rectangular operators between represented unit ranges

A possibly nonunital representation of a unital algebra has an actual unit
range. This file constructs the rectangular operator between two such ranges
and proves that an original compact intertwining defect remains compact.
No Fredholmness or global-index agreement is asserted by this construction.
-/

@[expose] public section

namespace NonUnitalStarAlgHom

universe uA uH₀ uH₁

variable {A : Type uA} [Semiring A] [Algebra ℂ A] [StarRing A]
variable {H₀ : Type uH₀} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
  [CompleteSpace H₀]
variable {H₁ : Type uH₁} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]

/-- Compress an actual rectangular operator to the two represented unit
ranges, using the target unit image and the original source inclusion. -/
noncomputable def unitRangeCompression
    (σ₀ : A →⋆ₙₐ[ℂ] (H₀ →L[ℂ] H₀))
    (σ₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁)) (T : H₀ →L[ℂ] H₁) :
    (σ₀ (1 : A)).range →L[ℂ] (σ₁ (1 : A)).range :=
  (σ₁ (1 : A)).rangeRestrict.comp (T.domRestrict ((σ₀ (1 : A)).range))

/-- The included supported value is the literal target unit image applied
to the original operator value. This permits zero or finite support. -/
@[simp]
theorem unitRangeCompression_apply
    (σ₀ : A →⋆ₙₐ[ℂ] (H₀ →L[ℂ] H₀))
    (σ₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁)) (T : H₀ →L[ℂ] H₁)
    (x : (σ₀ (1 : A)).range) :
    (unitRangeCompression σ₀ σ₁ T x : H₁) = σ₁ (1 : A) (T (x : H₀)) := rfl

/-- The supported intertwining defect factors through exactly the original
rectangular defect, followed by the actual target range map. -/
theorem unitRangeCompression_intertwining
    (σ₀ : A →⋆ₙₐ[ℂ] (H₀ →L[ℂ] H₀))
    (σ₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁)) (T : H₀ →L[ℂ] H₁) (a : A) :
    letI : CompleteSpace (σ₀ (1 : A)).range :=
      (ContinuousLinearMap.IsIdempotentElem.isClosed_range
        ((IsStarProjection.one A).map σ₀).isIdempotentElem).completeSpace_coe;
    letI : CompleteSpace (σ₁ (1 : A)).range :=
      (ContinuousLinearMap.IsIdempotentElem.isClosed_range
        ((IsStarProjection.one A).map σ₁).isIdempotentElem).completeSpace_coe;
    (unitRangeCompression σ₀ σ₁ T).comp (unitRangeStarAlgHom σ₀ a) -
        (unitRangeStarAlgHom σ₁ a).comp (unitRangeCompression σ₀ σ₁ T) =
      (σ₁ (1 : A)).rangeRestrict.comp
        ((T.comp (σ₀ a) - (σ₁ a).comp T).domRestrict ((σ₀ (1 : A)).range)) := by
  let : CompleteSpace (σ₀ (1 : A)).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      ((IsStarProjection.one A).map σ₀).isIdempotentElem).completeSpace_coe
  let : CompleteSpace (σ₁ (1 : A)).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      ((IsStarProjection.one A).map σ₁).isIdempotentElem).completeSpace_coe
  apply ContinuousLinearMap.ext
  intro x
  apply Subtype.ext
  have hleft (y : H₁) : σ₁ (1 : A) (σ₁ a y) = σ₁ a y := by
    have h : σ₁ (1 : A) * σ₁ a = σ₁ a := by
      rw [← map_mul σ₁ (1 : A) a, one_mul]
    exact congrArg (fun V : H₁ →L[ℂ] H₁ => V y) h
  have hright (y : H₁) : σ₁ a (σ₁ (1 : A) y) = σ₁ a y := by
    have h : σ₁ a * σ₁ (1 : A) = σ₁ a := by
      rw [← map_mul σ₁ a (1 : A), mul_one]
    exact congrArg (fun V : H₁ →L[ℂ] H₁ => V y) h
  change
    (unitRangeCompression σ₀ σ₁ T (unitRangeStarAlgHom σ₀ a x) : H₁) -
        (unitRangeStarAlgHom σ₁ a (unitRangeCompression σ₀ σ₁ T x) : H₁) =
      σ₁ (1 : A) (T (σ₀ a (x : H₀)) - σ₁ a (T (x : H₀)))
  simp only [unitRangeCompression_apply, unitRangeStarAlgHom_apply,
    map_sub, hleft, hright]

/-- An original compact intertwining defect stays compact on the actual
unit supports. Compactness is derived by the displayed factorization. -/
theorem unitRangeCompression_intertwining_compact
    (σ₀ : A →⋆ₙₐ[ℂ] (H₀ →L[ℂ] H₀))
    (σ₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁)) (T : H₀ →L[ℂ] H₁) (a : A)
    (h : IsCompactOperator (T.comp (σ₀ a) - (σ₁ a).comp T)) :
    letI : CompleteSpace (σ₀ (1 : A)).range :=
      (ContinuousLinearMap.IsIdempotentElem.isClosed_range
        ((IsStarProjection.one A).map σ₀).isIdempotentElem).completeSpace_coe;
    letI : CompleteSpace (σ₁ (1 : A)).range :=
      (ContinuousLinearMap.IsIdempotentElem.isClosed_range
        ((IsStarProjection.one A).map σ₁).isIdempotentElem).completeSpace_coe;
    IsCompactOperator
      ((unitRangeCompression σ₀ σ₁ T).comp (unitRangeStarAlgHom σ₀ a) -
        (unitRangeStarAlgHom σ₁ a).comp (unitRangeCompression σ₀ σ₁ T)) := by
  let : CompleteSpace (σ₀ (1 : A)).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      ((IsStarProjection.one A).map σ₀).isIdempotentElem).completeSpace_coe
  let : CompleteSpace (σ₁ (1 : A)).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
      ((IsStarProjection.one A).map σ₁).isIdempotentElem).completeSpace_coe
  rw [unitRangeCompression_intertwining]
  exact (h.comp_clm ((σ₀ (1 : A)).range.subtypeL)).clm_comp
    ((σ₁ (1 : A)).rangeRestrict)

end NonUnitalStarAlgHom
