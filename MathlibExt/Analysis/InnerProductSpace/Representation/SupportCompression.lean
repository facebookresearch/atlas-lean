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

public import Mathlib.Algebra.Star.StarAlgHom
public import Mathlib.Algebra.Star.StarProjection
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Idempotent
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict

/-!
# A unital representation on the actual range of the represented unit

A possibly nonunital complex star representation of a unital source algebra
restricts to a genuinely unital representation on the range of its unit image.
The support has the inherited Hilbert structure and completeness from the
closed range of the actual idempotent; no projector or new norm is constructed.
The source algebra need not be normed or complete. Zero support is permitted.
-/

@[expose] public section

namespace NonUnitalStarAlgHom

universe uA uH

variable {A : Type uA} [Semiring A] [Algebra ℂ A] [StarRing A]
variable {H : Type uH} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Restrict a possibly nonunital complex star representation to the actual
range of its represented unit. The resulting representation is unital there. -/
noncomputable def unitRangeStarAlgHom (σ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H)) :
    letI : CompleteSpace (σ (1 : A)).range :=
      (ContinuousLinearMap.IsIdempotentElem.isClosed_range
        ((IsStarProjection.one A).map σ).isIdempotentElem).completeSpace_coe;
    A →⋆ₐ[ℂ] ((σ (1 : A)).range →L[ℂ] (σ (1 : A)).range) := by
  let : CompleteSpace (σ (1 : A)).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
        ((IsStarProjection.one A).map σ).isIdempotentElem).completeSpace_coe
  let p : H →L[ℂ] H := σ (1 : A)
  let E : Submodule ℂ H := p.range
  have hp : IsStarProjection p := (IsStarProjection.one A).map σ
  have hMem (a : A) (x : H) : σ a x ∈ E := by
    refine ⟨σ a x, ?_⟩
    have hpa : p * σ a = σ a := by
      change σ (1 : A) * σ a = σ a
      rw [← map_mul σ (1 : A) a, one_mul]
    exact congrArg (fun T : H →L[ℂ] H => T x) hpa
  have hFix (x : E) : p (x : H) = (x : H) :=
    (LinearMap.IsIdempotentElem.isProj_range p.toLinearMap
      (ContinuousLinearMap.IsIdempotentElem.toLinearMap hp.isIdempotentElem)).map_id
      (x : H) x.property
  let r (a : A) : E →L[ℂ] E :=
    (σ a).restrict (fun x _ => hMem a x)
  exact
    { toFun a := (σ a).restrict (fun x _ => hMem a x)
      map_zero' := by
        apply ContinuousLinearMap.ext
        intro x
        apply Subtype.ext
        change σ (0 : A) (x : H) = 0
        exact congrArg (fun T : H →L[ℂ] H => T (x : H)) (map_zero σ)
      map_add' a b := by
        apply ContinuousLinearMap.ext
        intro x
        apply Subtype.ext
        change σ (a + b) (x : H) = σ a (x : H) + σ b (x : H)
        exact congrArg (fun T : H →L[ℂ] H => T (x : H)) (map_add σ a b)
      map_one' := by
        apply ContinuousLinearMap.ext
        intro x
        apply Subtype.ext
        change p (x : H) = (x : H)
        exact hFix x
      map_mul' a b := by
        apply ContinuousLinearMap.ext
        intro x
        apply Subtype.ext
        change σ (a * b) (x : H) = σ a (σ b (x : H))
        exact congrArg (fun T : H →L[ℂ] H => T (x : H)) (map_mul σ a b)
      commutes' z := by
        apply ContinuousLinearMap.ext
        intro x
        apply Subtype.ext
        change σ (algebraMap ℂ A z) (x : H) = z • (x : H)
        rw [Algebra.algebraMap_eq_smul_one, map_smul]
        change z • p (x : H) = z • (x : H)
        exact congrArg (fun y : H => z • y) (hFix x)
      map_star' a := by
        change r (star a) = star (r a)
        rw [ContinuousLinearMap.star_eq_adjoint]
        apply (ContinuousLinearMap.eq_adjoint_iff _ _).2
        intro x y
        change inner ℂ (σ (star a) (x : H)) (y : H) =
          inner ℂ (x : H) (σ a (y : H))
        rw [map_star σ a, ContinuousLinearMap.star_eq_adjoint]
        exact ContinuousLinearMap.adjoint_inner_left (σ a) (y : H) (x : H) }

/-- The included-vector action of the support representation is exactly
the original represented operator, not a newly chosen compression value. -/
@[simp]
theorem unitRangeStarAlgHom_apply (σ : A →⋆ₙₐ[ℂ] (H →L[ℂ] H))
    (a : A) (x : (σ (1 : A)).range) :
    letI : CompleteSpace (σ (1 : A)).range :=
      (ContinuousLinearMap.IsIdempotentElem.isClosed_range
        ((IsStarProjection.one A).map σ).isIdempotentElem).completeSpace_coe;
    (unitRangeStarAlgHom σ a x : H) = σ a (x : H) := by
  let : CompleteSpace (σ (1 : A)).range :=
    (ContinuousLinearMap.IsIdempotentElem.isClosed_range
        ((IsStarProjection.one A).map σ).isIdempotentElem).completeSpace_coe
  rfl

end NonUnitalStarAlgHom
