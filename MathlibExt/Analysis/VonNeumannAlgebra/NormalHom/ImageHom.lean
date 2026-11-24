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

public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.ImageVonNeumannAlgebra
public import MathlibExt.Analysis.VonNeumannAlgebra.NormalHom.VectorFunctionalCriterion

/-!
# The computed normal map onto the literal von Neumann image

The original operator star map is restricted to its actual range carrier.
Its vector-functional pullbacks are the same original normal-map
pullbacks, so the computed map is normal. Original injectivity and literal
range membership prove it is bijective. No surjectivity, normality, image,
predual or inverse certificate is supplied.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

open scoped CStarAlgebra InnerProductSpace

namespace VonNeumannAlgebra.NormalStarAlgHom

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {K : Type v} [NormedAddCommGroup K] [InnerProductSpace ℂ K] [CompleteSpace K]
variable {M : VonNeumannAlgebra H} {N : VonNeumannAlgebra K}

/-- Restrict the original normal operator map to its literal constructed VN range. -/
def toImage (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    NormalStarAlgHom M (f.imageVonNeumannAlgebra hf) := by
  let g : M →⋆ₐ[ℂ] (K →L[ℂ] K) := N.toStarSubalgebra.subtype.comp f.toStarAlgHom
  let F : M →⋆ₐ[ℂ] f.imageVonNeumannAlgebra hf := g.rangeRestrict
  refine ofVectorFunctionalPullbacks F ?_
  intro ξ η
  have heq : (vectorFunctional (f.imageVonNeumannAlgebra hf) ξ η).comp
      (⟨LinearMap.ofClass F, map_continuous F⟩ : M →L[ℂ] f.imageVonNeumannAlgebra hf) =
      (f.predualPullback (normalVectorFunctional N ξ η) : StrongDual ℂ M) := by
    apply ContinuousLinearMap.ext
    intro a
    rw [ContinuousLinearMap.comp_apply, vectorFunctional_apply, f.predualPullback_apply]
    change ⟪ξ, (f a : K →L[ℂ] K) η⟫_ℂ =
      (normalVectorFunctional N ξ η : StrongDual ℂ N) (f a)
    exact (vectorFunctional_apply N ξ η (f a)).symm
  rw [heq]
  exact (f.predualPullback (normalVectorFunctional N ξ η)).property

/-- The computed normal range restriction keeps every original operator value. -/
@[simp]
theorem toImage_apply (f : NormalStarAlgHom M N) (hf : Function.Injective f) (a : M) :
    (f.toImage hf a : K →L[ℂ] K) = (f a : K →L[ℂ] K) := rfl

/-- Original injectivity proves injectivity of the same computed image map. -/
theorem toImage_injective (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    Function.Injective (f.toImage hf) := by
  intro a b h
  apply hf
  apply Subtype.ext
  have hvalue := congrArg (fun p : f.imageVonNeumannAlgebra hf => (p : K →L[ℂ] K)) h
  simpa only [toImage_apply] using hvalue

/-- Every actual image carrier element has an original source preimage under the computed map. -/
theorem toImage_surjective (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    Function.Surjective (f.toImage hf) := by
  intro b
  have hb : (b : K →L[ℂ] K) ∈ Set.range (fun a : M => (f a : K →L[ℂ] K)) :=
    Eq.mp (congrArg (fun s : Set (K →L[ℂ] K) => (b : K →L[ℂ] K) ∈ s)
      (f.coe_imageVonNeumannAlgebra hf)) b.property
  obtain ⟨a, ha⟩ := hb
  change (f a : K →L[ℂ] K) = (b : K →L[ℂ] K) at ha
  refine ⟨a, ?_⟩
  apply Subtype.ext
  simpa only [toImage_apply] using ha

end

end VonNeumannAlgebra.NormalStarAlgHom
