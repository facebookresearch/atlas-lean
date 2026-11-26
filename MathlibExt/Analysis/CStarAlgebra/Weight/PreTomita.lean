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

public import MathlibExt.Analysis.CStarAlgebra.Weight.GNSCompletion
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Star.Module

/-!
# The pre-Tomita involution on the finite star GNS domain

Let `φ` be a faithful extended positive weight on a nonunital complex C-star algebra `A`, and `Λ
: n_φ → H_φ` its GNS map. The nonunital star algebra `D_φ={x ∈ n_φ : x* ∈ n_φ}` maps injectively
into `H_φ`. Its image `C_φ=Λ(D_φ)` is a complex submodule with the norm inherited from `H_φ`.

The conjugate-linear involution `S₀ : C_φ → C_φ` is characterized by `S₀Λ(x)=Λ(x*)`. Its
inclusion into `H_φ` gives an injective semilinear operator with domain `C_φ`. Neither density
of this domain nor continuity or closability of `S₀` is assumed or established here.

Source: Connes, Noncommutative Geometry (1994), V.3 Definition 6 and the NSF-weight algebra
paragraph, OCR 14358--14386, SHA256
e968b4b9604a8b9a789a202dbb0f241793c10958a8a6962bc367e67a4820b9b3. The inner-product convention
here is linear in the second argument, so the algebra pairing is `φ(x* y)` rather than `φ(y*
x)`.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CStarAlgebra.ScalarWeight

noncomputable section

universe u

variable {A : Type u} [NonUnitalCStarAlgebra A]

/-- **GNS map of the finite star algebra.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. Let
`H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear map `Λ :
n_φ → H_φ`. put `D_φ={x ∈ n_φ : x* ∈ n_φ}`. The complex-linear map `finiteStarSquareGNSMap φ :
D_φ → H_φ` is the restriction of `Λ` to this nonunital star algebra. -/
def Weight.finiteStarSquareGNSMap (φ : Weight A) : φ.finiteStarSquareSubalgebra →ₗ[ℂ] φ.GNS :=
  φ.gnsMap.comp (LinearMap.codRestrict φ.finiteSquareSubmodule
    φ.finiteStarSquareSubalgebra.toSubmodule.subtype fun x => x.property.1)

/-- **GNS value of a finite star element.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. Let
`H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear map `Λ :
n_φ → H_φ`. for `x : D_φ={x ∈ n_φ : x* ∈ n_φ}`, `finiteStarSquareGNSMap φ x=Λ(x)`, with `x`
regarded as a member of `n_φ`. -/
@[simp]
theorem Weight.finiteStarSquareGNSMap_apply (φ : Weight A) (x : φ.finiteStarSquareSubalgebra) :
    φ.finiteStarSquareGNSMap x = φ.gnsMap ⟨(x : A), x.property.1⟩ :=
  rfl

/-- **Faithful GNS map on the finite star algebra.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. the
restriction `Λ : D_φ → H_φ`, where `D_φ={x ∈ n_φ : x* ∈ n_φ}`, is injective. -/
theorem Weight.finiteStarSquareGNSMap_injective (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Injective φ.finiteStarSquareGNSMap := by
  intro x y hxy
  apply Subtype.ext
  have h := φ.gnsMap_injective hφ hxy
  exact congrArg (fun z : φ.finiteSquareSubmodule => (z : A)) h

/-- **GNS image of the finite star algebra.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. for `D_φ={x ∈ n_φ : x* ∈ n_φ}`, `tomitaCore φ` is the complex submodule
`C_φ=Λ(D_φ)` of `H_φ`; its norm is inherited from the Hilbert completion. -/
def Weight.tomitaCore (φ : Weight A) : Submodule ℂ φ.GNS :=
  LinearMap.range φ.finiteStarSquareGNSMap

/-- **Membership in the pre-Tomita domain.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. write `D_φ={x ∈ n_φ : x* ∈ n_φ}`. A vector `ξ ∈ H_φ` belongs to
`tomitaCore φ` exactly when `ξ=Λ(x)` for some `x ∈ D_φ`. -/
theorem Weight.mem_tomitaCore (φ : Weight A) (ξ : φ.GNS) :
    ξ ∈ φ.tomitaCore ↔ ∃ x : φ.finiteStarSquareSubalgebra, φ.finiteStarSquareGNSMap x = ξ :=
  Iff.rfl

/-- **Linear identification of the finite star GNS image.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. `tomitaCoreEquiv φ` is the complex-linear equivalence `e`, whose
inverse recovers the unique finite star element with a given GNS image. -/
def Weight.tomitaCoreEquiv (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.finiteStarSquareSubalgebra ≃ₗ[ℂ] φ.tomitaCore :=
  LinearEquiv.ofInjective φ.finiteStarSquareGNSMap (φ.finiteStarSquareGNSMap_injective hφ)

/-- **Hilbert value of the finite star image equivalence.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `x ∈ D_φ`, the vector of `H_φ` underlying `tomitaCoreEquiv φ x`
is `Λ(x)`. -/
@[simp]
theorem Weight.tomitaCoreEquiv_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    (φ.tomitaCoreEquiv hφ x : φ.GNS) = φ.finiteStarSquareGNSMap x :=
  rfl

/-- **Conjugate-linear involution of the GNS core.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. `preTomitaCore φ : C_φ ≃ₗ⋆[ℂ] C_φ` is `S₀=e ∘ star ∘ e⁻¹`, so
`S₀Λ(x)=Λ(x*)`. No boundedness is asserted. -/
def Weight.preTomitaCore (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.tomitaCore ≃ₗ⋆[ℂ] φ.tomitaCore :=
  ((φ.tomitaCoreEquiv hφ).symm.trans (starLinearEquiv ℂ)).trans (φ.tomitaCoreEquiv hφ)

/-- **Pre-Tomita involution on a finite star vector.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `x ∈ D_φ`, `preTomitaCore φ (e(x))=e(x*)`, equivalently
`S₀Λ(x)=Λ(x*)`. -/
theorem Weight.preTomitaCore_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    φ.preTomitaCore hφ (φ.tomitaCoreEquiv hφ x) = φ.tomitaCoreEquiv hφ (star x) := by
  change φ.tomitaCoreEquiv hφ (star ((φ.tomitaCoreEquiv hφ).symm (φ.tomitaCoreEquiv hφ x))) = _
  rw [LinearEquiv.symm_apply_apply]

/-- **Square of the pre-Tomita involution.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. `S₀=preTomitaCore φ` satisfies `S₀(S₀ξ)=ξ` for every `ξ ∈ C_φ`. -/
theorem Weight.preTomitaCore_involutive (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Involutive (φ.preTomitaCore hφ) := by
  intro ξ
  change φ.tomitaCoreEquiv hφ
    (star ((φ.tomitaCoreEquiv hφ).symm
      (φ.tomitaCoreEquiv hφ (star ((φ.tomitaCoreEquiv hφ).symm ξ))))) = ξ
  rw [LinearEquiv.symm_apply_apply, star_star, LinearEquiv.apply_symm_apply]

/-- **Semilinear pre-Tomita operator into the Hilbert space.** Let `A` be a nonunital complex
C-star algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real
homogeneous weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x*
x)).toReal` for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with
dense complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every
positive `a : A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear
equivalence `e : D_φ ≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. `preTomitaOperator φ : C_φ →ₗ⋆[ℂ] H_φ` is the
inclusion of `S₀=e ∘ star ∘ e⁻¹`, with value `Λ(x*)` on `e(x)`. -/
def Weight.preTomitaOperator (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    φ.tomitaCore →ₗ⋆[ℂ] φ.GNS :=
  φ.tomitaCore.subtype.comp (φ.preTomitaCore hφ).toLinearMap

/-- **Pre-Tomita operator on a finite star element.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `x ∈ D_φ`, `preTomitaOperator φ (e(x))=Λ(x*)` in `H_φ`. -/
theorem Weight.preTomitaOperator_apply (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x : φ.finiteStarSquareSubalgebra) :
    φ.preTomitaOperator hφ (φ.tomitaCoreEquiv hφ x) = φ.finiteStarSquareGNSMap (star x) := by
  change (φ.preTomitaCore hφ (φ.tomitaCoreEquiv hφ x) : φ.GNS) = _
  rw [φ.preTomitaCore_apply]
  rfl

/-- **Injectivity of the pre-Tomita operator.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. `preTomitaOperator φ : C_φ → H_φ` is injective, as the involution of `C_φ`
followed by its inclusion in `H_φ`. -/
theorem Weight.preTomitaOperator_injective (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    Function.Injective (φ.preTomitaOperator hφ) :=
  Subtype.coe_injective.comp (φ.preTomitaCore hφ).injective

end

end CStarAlgebra.ScalarWeight
