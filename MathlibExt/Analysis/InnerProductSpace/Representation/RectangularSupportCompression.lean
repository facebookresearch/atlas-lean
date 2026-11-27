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
# Rectangular compression between represented unit supports

For possibly nonunital representations `σ_i : A → B(H_i)` of a unital complex algebra with
star-ring involution, let `p_i=σ_i(1)`. A bounded operator `T : H₀ → H₁` compresses to `C :
range p₀ → range p₁`, `Cx=p₁(Tx)`.

For each coefficient `a`, its supported intertwining defect is `C σ₀^p(a)-σ₁^p(a) C =
p₁(Tσ₀(a)-σ₁(a)T)|_(range p₀)`. Thus compactness of the full defect implies compactness of the
compressed defect. Both Hilbert spaces are complete; no coefficient norm, Fredholmness or index
comparison is imposed.
-/

@[expose] public section

namespace NonUnitalStarAlgHom

universe uA uH₀ uH₁

variable {A : Type uA} [Semiring A] [Algebra ℂ A] [StarRing A]
variable {H₀ : Type uH₀} [NormedAddCommGroup H₀] [InnerProductSpace ℂ H₀]
  [CompleteSpace H₀]
variable {H₁ : Type uH₁} [NormedAddCommGroup H₁] [InnerProductSpace ℂ H₁]
  [CompleteSpace H₁]

/-- **Bounded operator between represented unit ranges.** Let `A` be a unital semiring with a
complex algebra structure and star-ring involution, `H₀,H₁` complete complex Hilbert
spaces, `σ_i : A →⋆ₙₐ[ℂ] B(H_i)` possibly nonunital representations, and `T : H₀ →L[ℂ]
H₁`. Put `p_i=σ_i(1)` and `C : range p₀ → range p₁`, `Cx=p₁(Tx)`. `unitRangeCompression σ₀
σ₁ T` is `C`, using the subspace norms and the complete Hilbert structures of the
projection ranges. -/
noncomputable def unitRangeCompression
    (σ₀ : A →⋆ₙₐ[ℂ] (H₀ →L[ℂ] H₀))
    (σ₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁)) (T : H₀ →L[ℂ] H₁) :
    (σ₀ (1 : A)).range →L[ℂ] (σ₁ (1 : A)).range :=
  (σ₁ (1 : A)).rangeRestrict.comp (T.domRestrict ((σ₀ (1 : A)).range))

/-- **Included-vector value of rectangular support compression.** Let `A` be a unital semiring
with a complex algebra structure and star-ring involution, `H₀,H₁` complete complex
Hilbert spaces, `σ_i : A →⋆ₙₐ[ℂ] B(H_i)` possibly nonunital representations, and `T : H₀
→L[ℂ] H₁`. Put `p_i=σ_i(1)` and `C : range p₀ → range p₁`, `Cx=p₁(Tx)`. for `x ∈ range
p₀`, the vector of `H₁` underlying `unitRangeCompression σ₀ σ₁ T x` is `p₁(Tx)`. -/
@[simp]
theorem unitRangeCompression_apply
    (σ₀ : A →⋆ₙₐ[ℂ] (H₀ →L[ℂ] H₀))
    (σ₁ : A →⋆ₙₐ[ℂ] (H₁ →L[ℂ] H₁)) (T : H₀ →L[ℂ] H₁)
    (x : (σ₀ (1 : A)).range) :
    (unitRangeCompression σ₀ σ₁ T x : H₁) = σ₁ (1 : A) (T (x : H₀)) := rfl

/-- **Factorization of a supported intertwining defect.** Let `A` be a unital semiring with a
complex algebra structure and star-ring involution, `H₀,H₁` complete complex Hilbert
spaces, `σ_i : A →⋆ₙₐ[ℂ] B(H_i)` possibly nonunital representations, and `T : H₀ →L[ℂ]
H₁`. Put `p_i=σ_i(1)` and `C : range p₀ → range p₁`, `Cx=p₁(Tx)`. let `σ_i^p` denote
`unitRangeStarAlgHom σ_i`. For `a ∈ A`, `C σ₀^p(a)-σ₁^p(a) C = p₁(Tσ₀(a)-σ₁(a)T)|_(range
p₀)`, with codomain `range p₁`. -/
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

/-- **Compactness passes to the represented-support defect.** Let `A` be a unital semiring
with a complex algebra structure and star-ring involution, `H₀,H₁` complete complex
Hilbert spaces, `σ_i : A →⋆ₙₐ[ℂ] B(H_i)` possibly nonunital representations, and `T : H₀
→L[ℂ] H₁`. Put `p_i=σ_i(1)` and `C : range p₀ → range p₁`, `Cx=p₁(Tx)`. for `a ∈ A`, if
`Tσ₀(a)-σ₁(a)T` is compact, then `C σ₀^p(a)-σ₁^p(a) C` is compact, where
`σ_i^p=unitRangeStarAlgHom σ_i`. -/
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
