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
# Normal homomorphism onto the concrete image algebra

Let `f : M → N` be an injective normal unital complex star homomorphism. Restricting its
codomain to the von Neumann algebra `R={f(x) : x ∈ M}` gives a normal homomorphism `M → R`.

This map is injective and surjective, and its operator value at `x` is `f(x)`. Its normality and
surjectivity are conclusions, not extra assumptions on the image map.
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

/-- **Normal range restriction of an injective homomorphism.** Let `M,N` be concrete von
Neumann algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. `f.toImage : NormalStarAlgHom M R`
sends `x` to the element represented by `f(x)` in the von Neumann image algebra `R`. -/
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

/-- **Operator value of the normal image map.** Let `M,N` be concrete von Neumann algebras on
complete complex Hilbert spaces. Their normal-functional Banach spaces `M_*,N_*` are the
norm-closed spans of vector functionals, and their ultraweak topologies are `σ(M,M_*)`,
`σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is ultraweakly
continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for its operator
range on the target Hilbert space `K`. for `x ∈ M`, the bounded operator underlying
`f.toImage x` is `(f(x) : B(K))`. -/
@[simp]
theorem toImage_apply (f : NormalStarAlgHom M N) (hf : Function.Injective f) (a : M) :
    (f.toImage hf a : K →L[ℂ] K) = (f a : K →L[ℂ] K) := rfl

/-- **Injectivity of the normal map into its image.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. the range-restricted map `f.toImage :
M → R` is injective. -/
theorem toImage_injective (f : NormalStarAlgHom M N) (hf : Function.Injective f) :
    Function.Injective (f.toImage hf) := by
  intro a b h
  apply hf
  apply Subtype.ext
  have hvalue := congrArg (fun p : f.imageVonNeumannAlgebra hf => (p : K →L[ℂ] K)) h
  simpa only [toImage_apply] using hvalue

/-- **Surjectivity of the normal map into its image.** Let `M,N` be concrete von Neumann
algebras on complete complex Hilbert spaces. Their normal-functional Banach spaces
`M_*,N_*` are the norm-closed spans of vector functionals, and their ultraweak topologies
are `σ(M,M_*)`, `σ(N,N_*)`. Let `f : M → N` be a unital complex star homomorphism that is
ultraweakly continuous. Assume `f` is injective. Write `R={ (f(x) : B(K)) : x ∈ M }` for
its operator range on the target Hilbert space `K`. the range-restricted map `f.toImage :
M → R` is surjective; every element of the image algebra has a source preimage. -/
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
