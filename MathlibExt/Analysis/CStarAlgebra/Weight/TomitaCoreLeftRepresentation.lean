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

public import MathlibExt.Analysis.CStarAlgebra.Weight.TomitaCoreAlgebra
public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSLeftRepresentation

/-!
# Bounded left representation of the finite GNS core algebra

For a faithful extended positive weight on a nonunital complex C-star algebra, identify `D_φ={x
: φ(x* x)<∞ ∧ φ(x x*)<∞}` with its GNS image `C_φ`. For `ξ=Λ(a)` in this core, set
`λ_φ(ξ)=π_φ(a)`, where `π_φ` is the bounded GNS left representation of `A`.

This is a nonunital complex star homomorphism `C_φ → B(H_φ)`. It obeys `λ_φ(Λ(a))Λ(x)=Λ(a*x)`
for `x ∈ n_φ` and preserves the core with `λ_φ(ξ)η=ξ ⋅ η`. Density of the core or boundedness of
its involution is not required.

Source: Connes, Noncommutative Geometry (1994), V.3 Definition 6 and the `A_φ` paragraph, OCR
14358--14386.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **Bounded left star representation of the GNS core.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. `λ_φ=tomitaCoreLeftRepresentation φ : C_φ →⋆ₙₐ[ℂ] B(H_φ)` sends `ξ`
to `π_φ((e⁻¹ξ : A))`, where `π_φ` is the GNS left representation of `A`. -/
def Weight.tomitaCoreLeftRepresentation (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCore →⋆ₙₐ[ℂ] (φ.GNS →L[ℂ] φ.GNS) := by
  letI := φ.tomitaCoreNonUnitalRing hφ
  letI := φ.tomitaCoreStar hφ
  exact (φ.gnsLeftRepresentation.comp
    (NonUnitalStarSubalgebraClass.subtype φ.finiteStarSquareSubalgebra)).comp
      (φ.fromTomitaCoreStarAlgHom hφ)

/-- **Bounded operator of a core vector.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. Let
`H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear map `Λ :
n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put `D_φ={x ∈ n_φ
: x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`.
for `ξ ∈ C_φ`, `tomitaCoreLeftRepresentation φ ξ=gnsLeftRepresentation φ ((e⁻¹ξ : A))`. -/
@[simp]
theorem Weight.tomitaCoreLeftRepresentation_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ : φ.tomitaCore) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCoreLeftRepresentation hφ ξ =
      φ.gnsLeftRepresentation ((φ.tomitaCoreEquiv hφ).symm ξ : A) := by
  let := φ.tomitaCoreNonUnitalRing hφ
  let := φ.tomitaCoreStar hφ
  rfl

/-- **Left representation of a finite star element.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `a ∈ D_φ`, `tomitaCoreLeftRepresentation φ
(e(a))=gnsLeftRepresentation φ (a : A)`. -/
theorem Weight.tomitaCoreLeftRepresentation_original (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (a : φ.finiteStarSquareSubalgebra) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCoreLeftRepresentation hφ (φ.tomitaCoreEquiv hφ a) = φ.gnsLeftRepresentation (a : A) := by
  let := φ.tomitaCoreNonUnitalRing hφ
  let := φ.tomitaCoreStar hφ
  rw [φ.tomitaCoreLeftRepresentation_apply, LinearEquiv.symm_apply_apply]

/-- **Core coefficient acting on a finite square vector.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `ξ ∈ C_φ` and `x ∈ n_φ`, `tomitaCoreLeftRepresentation φ ξ (Λ
x)=Λ((e⁻¹ξ : A) * x)`. -/
theorem Weight.tomitaCoreLeftRepresentation_gnsMap (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ : φ.tomitaCore) (x : φ.finiteSquareSubmodule) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCoreLeftRepresentation hφ ξ (φ.gnsMap x) =
      φ.gnsMap (φ.finiteSquareLeftMul ((φ.tomitaCoreEquiv hφ).symm ξ : A) x) := by
  let := φ.tomitaCoreNonUnitalRing hφ
  let := φ.tomitaCoreStar hφ
  rw [φ.tomitaCoreLeftRepresentation_apply]
  exact φ.gnsLeftRepresentation_gnsMap _ x

/-- **Left representation agrees with the core product.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `ξ,η ∈ C_φ`, `tomitaCoreLeftRepresentation φ ξ (η : H_φ)=(ξ ⋅ η :
H_φ)`, where `ξ ⋅ η=e(e⁻¹ξ * e⁻¹η)`. -/
theorem Weight.tomitaCoreLeftRepresentation_coreAction (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ η : φ.tomitaCore) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCoreLeftRepresentation hφ ξ (η : φ.GNS) = (φ.tomitaCoreProduct hφ ξ η : φ.GNS) := by
  let := φ.tomitaCoreNonUnitalRing hφ
  let := φ.tomitaCoreStar hφ
  obtain ⟨a, rfl⟩ := (φ.tomitaCoreEquiv hφ).surjective ξ
  obtain ⟨x, rfl⟩ := (φ.tomitaCoreEquiv hφ).surjective η
  rw [φ.tomitaCoreLeftRepresentation_original, φ.tomitaCoreProduct_original,
    φ.tomitaCoreEquiv_apply, φ.tomitaCoreEquiv_apply,
    φ.finiteStarSquareGNSMap_apply, φ.finiteStarSquareGNSMap_apply]
  rw [φ.gnsLeftRepresentation_gnsMap]
  rfl

end

end CStarAlgebra.ScalarWeight
