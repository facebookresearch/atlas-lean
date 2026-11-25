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

public import MathlibExt.Analysis.CStarAlgebra.Weight.PreTomita
public import Mathlib.Algebra.Ring.InjSurj
public import Mathlib.Algebra.Star.StarAlgHom

/-!
# Algebra structure on the finite star GNS image

For a faithful extended positive weight on a nonunital complex C-star algebra, the GNS map
identifies the finite star algebra `D_φ={x : φ(x* x)<∞ ∧ φ(x x*)<∞}` with its image `C_φ` in
`H_φ`. Transporting its operations gives `Λ(x)Λ(y)=Λ(x*y)` and `Λ(x)*=Λ(x*)` on the image.

These operations make `C_φ` a nonunital complex star algebra while retaining its Hilbert-space
addition, scalar action and subspace norm. No submultiplicative estimate for that norm,
continuity of the involution or completeness of the core algebra is asserted.

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

/-- **Product of finite star GNS vectors.** Let `A` be a nonunital complex C-star algebra with its
spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight vanishing
at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈ n_φ`. Let
`H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear map `Λ :
n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put `D_φ={x ∈ n_φ
: x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`.
define `ξ ⋅ η = e(e⁻¹ξ * e⁻¹η)` on `C_φ`; in particular, `Λ(x) ⋅ Λ(y)=Λ(x*y)`. -/
def Weight.tomitaCoreProduct (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ η : φ.tomitaCore) : φ.tomitaCore :=
  φ.tomitaCoreEquiv hφ ((φ.tomitaCoreEquiv hφ).symm ξ * (φ.tomitaCoreEquiv hφ).symm η)

/-- **Algebra preimage of the GNS core product.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. for `ξ,η ∈ C_φ`, `e⁻¹(tomitaCoreProduct φ ξ η)=e⁻¹ξ * e⁻¹η` in `D_φ`. -/
theorem Weight.tomitaCoreProduct_inverse (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ η : φ.tomitaCore) :
    (φ.tomitaCoreEquiv hφ).symm (φ.tomitaCoreProduct hφ ξ η) =
      (φ.tomitaCoreEquiv hφ).symm ξ * (φ.tomitaCoreEquiv hφ).symm η := by
  exact (φ.tomitaCoreEquiv hφ).symm_apply_apply _

/-- **GNS image of a finite star algebra product.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. for `x,y ∈ D_φ`, `tomitaCoreProduct φ (e(x)) (e(y))=e(x*y)`. -/
theorem Weight.tomitaCoreProduct_original (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (x y : φ.finiteStarSquareSubalgebra) :
    φ.tomitaCoreProduct hφ (φ.tomitaCoreEquiv hφ x) (φ.tomitaCoreEquiv hφ y) =
      φ.tomitaCoreEquiv hφ (x * y) := by
  change φ.tomitaCoreEquiv hφ
    ((φ.tomitaCoreEquiv hφ).symm (φ.tomitaCoreEquiv hφ x) *
      (φ.tomitaCoreEquiv hφ).symm (φ.tomitaCoreEquiv hφ y)) = _
  rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- **Nonunital ring on the finite star GNS image.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. `C_φ` is a nonunital ring for the product `ξ ⋅ η=e(e⁻¹ξ * e⁻¹η)`, with
addition, zero and negation inherited from the Hilbert space. -/
@[instance_reducible]
def Weight.tomitaCoreNonUnitalRing (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    NonUnitalRing φ.tomitaCore := by
  letI : Mul φ.tomitaCore := ⟨φ.tomitaCoreProduct hφ⟩
  let e := (φ.tomitaCoreEquiv hφ).symm
  exact Function.Injective.nonUnitalRing e e.injective
    (map_zero e) (fun ξ η => map_add e ξ η)
    (fun ξ η => φ.tomitaCoreProduct_inverse hφ ξ η)
    (fun ξ => map_neg e ξ) (fun ξ η => map_sub e ξ η)
    (fun n ξ => map_nsmul e n ξ) (fun n ξ => map_zsmul e n ξ)

/-- **Hilbert addition retained by the GNS core ring.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. the additive commutative group underlying `tomitaCoreNonUnitalRing φ`
equals the additive group of the complex submodule `C_φ ⊆ H_φ`. -/
theorem Weight.tomitaCoreNonUnitalRing_addGroup (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    (φ.tomitaCoreNonUnitalRing hφ).toAddCommGroup =
      (inferInstance : AddCommGroup φ.tomitaCore) :=
  rfl

/-- **Star operation on the finite GNS core.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. the involution on `C_φ` is `ξ ↦ e((e⁻¹ξ)*)`, which sends `Λ(x)` to `Λ(x*)`. -/
@[instance_reducible]
def Weight.tomitaCoreStar (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) : Star φ.tomitaCore where
  star := φ.preTomitaCore hφ

/-- **Algebra preimage of the pre-Tomita involution.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `ξ ∈ C_φ`, `e⁻¹(preTomitaCore φ ξ)=(e⁻¹ξ)*` in `D_φ`. -/
theorem Weight.preTomitaCore_inverse (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (ξ : φ.tomitaCore) :
    (φ.tomitaCoreEquiv hφ).symm (φ.preTomitaCore hφ ξ) =
      star ((φ.tomitaCoreEquiv hφ).symm ξ) := by
  change (φ.tomitaCoreEquiv hφ).symm
    (φ.tomitaCoreEquiv hφ (star ((φ.tomitaCoreEquiv hφ).symm ξ))) = _
  exact (φ.tomitaCoreEquiv hφ).symm_apply_apply _

/-- **Star ring laws on the finite GNS core.** Let `A` be a nonunital complex C-star algebra with
its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. for the transported product and involution, `star(ξ+η)=star ξ+star η`,
`star(ξ ⋅ η)=star η ⋅ star ξ`, and `star(star ξ)=ξ`. -/
@[instance_reducible]
def Weight.tomitaCoreStarRing (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    StarRing φ.tomitaCore := by
  letI := φ.tomitaCoreNonUnitalRing hφ
  letI := φ.tomitaCoreStar hφ
  let e := (φ.tomitaCoreEquiv hφ).symm
  exact Function.Injective.starRing e e.injective
    (fun ξ => φ.preTomitaCore_inverse hφ ξ)
    (fun ξ η => map_add e ξ η)
    (fun ξ η => φ.tomitaCoreProduct_inverse hφ ξ η)

/-- **Conjugate scalar compatibility on the GNS core.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for the involution `ξ*=e((e⁻¹ξ)*)`, `(c • ξ)*=conj(c) • ξ*` for `c :
ℂ` and `ξ ∈ C_φ`. -/
theorem Weight.tomitaCoreStarModule (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreStar hφ;
    StarModule ℂ φ.tomitaCore := by
  let := φ.tomitaCoreStar hφ
  let e := (φ.tomitaCoreEquiv hφ).symm
  exact Function.Injective.starModule e ℂ e.injective
    (fun ξ => φ.preTomitaCore_inverse hφ ξ)
    (fun c ξ => e.map_smul c ξ)

/-- **Complex scalar in the first core product factor.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `c : ℂ` and `ξ,η ∈ C_φ`, `(c • ξ) ⋅ η=c • (ξ ⋅ η)`, where `ξ ⋅
η=e(e⁻¹ξ * e⁻¹η)`. -/
theorem Weight.tomitaCoreProduct_smul_left (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (c : ℂ) (ξ η : φ.tomitaCore) :
    φ.tomitaCoreProduct hφ (c • ξ) η = c • φ.tomitaCoreProduct hφ ξ η := by
  apply (φ.tomitaCoreEquiv hφ).symm.injective
  simpa only [φ.tomitaCoreProduct_inverse, map_smul] using
    smul_mul_assoc c ((φ.tomitaCoreEquiv hφ).symm ξ) ((φ.tomitaCoreEquiv hφ).symm η)

/-- **Complex scalar in the second core product factor.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. for `c : ℂ` and `ξ,η ∈ C_φ`, `ξ ⋅ (c • η)=c • (ξ ⋅ η)`, where `ξ ⋅
η=e(e⁻¹ξ * e⁻¹η)`. -/
theorem Weight.tomitaCoreProduct_smul_right (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0)
    (c : ℂ) (ξ η : φ.tomitaCore) :
    φ.tomitaCoreProduct hφ ξ (c • η) = c • φ.tomitaCoreProduct hφ ξ η := by
  apply (φ.tomitaCoreEquiv hφ).symm.injective
  simpa only [φ.tomitaCoreProduct_inverse, map_smul] using
    mul_smul_comm c ((φ.tomitaCoreEquiv hφ).symm ξ) ((φ.tomitaCoreEquiv hφ).symm η)

/-- **Star algebra map onto the finite GNS image.** Let `A` be a nonunital complex C-star algebra
with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous weight
vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal` for `x ∈
n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense complex-linear
map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a : A`. Put
`D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ ≃ₗ[ℂ]
C_φ`, `e(x)=Λ(x)`. the identification `e(x)=Λ(x)` defines a nonunital complex star
homomorphism `D_φ → C_φ` for the transported product and involution. -/
def Weight.toTomitaCoreStarAlgHom (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.finiteStarSquareSubalgebra →⋆ₙₐ[ℂ] φ.tomitaCore := by
  letI := φ.tomitaCoreNonUnitalRing hφ
  letI := φ.tomitaCoreStar hφ
  refine
    { toFun := φ.tomitaCoreEquiv hφ
      map_zero' := map_zero (φ.tomitaCoreEquiv hφ)
      map_add' := fun x y => map_add (φ.tomitaCoreEquiv hφ) x y
      map_mul' := fun x y => (φ.tomitaCoreProduct_original hφ x y).symm
      map_smul' := fun c x => (φ.tomitaCoreEquiv hφ).map_smul c x
      map_star' := fun x => (φ.preTomitaCore_apply hφ x).symm }

/-- **Inverse star algebra map from the finite GNS image.** Let `A` be a nonunital complex C-star
algebra with its spectral order and `φ : A₊ → [0,∞]` an additive, nonnegative-real homogeneous
weight vanishing at zero. Write `n_φ = {x ∈ A : φ(x* x) < ∞}`. Put `q(x) = (φ(x* x)).toReal`
for `x ∈ n_φ`. Let `H_φ` be the Hilbert completion for the seminorm `√q(x)`, with dense
complex-linear map `Λ : n_φ → H_φ`. Assume faithfulness: `φ(a)=0 → a=0` for every positive `a
: A`. Put `D_φ={x ∈ n_φ : x* ∈ n_φ}` and `C_φ=Λ(D_φ) ⊆ H_φ`, with linear equivalence `e : D_φ
≃ₗ[ℂ] C_φ`, `e(x)=Λ(x)`. `e⁻¹ : C_φ → D_φ` is a nonunital complex star homomorphism,
recovering the unique finite star element whose image is the given core vector. -/
def Weight.fromTomitaCoreStarAlgHom (φ : Weight A)
    (hφ : ∀ a : PositiveElement A, φ.value a = 0 → (a : A) = 0) :
    letI := φ.tomitaCoreNonUnitalRing hφ;
    letI := φ.tomitaCoreStar hφ;
    φ.tomitaCore →⋆ₙₐ[ℂ] φ.finiteStarSquareSubalgebra := by
  letI := φ.tomitaCoreNonUnitalRing hφ
  letI := φ.tomitaCoreStar hφ
  refine
    { toFun := (φ.tomitaCoreEquiv hφ).symm
      map_zero' := map_zero (φ.tomitaCoreEquiv hφ).symm
      map_add' := fun ξ η => map_add (φ.tomitaCoreEquiv hφ).symm ξ η
      map_mul' := fun ξ η => φ.tomitaCoreProduct_inverse hφ ξ η
      map_smul' := fun c ξ => (φ.tomitaCoreEquiv hφ).symm.map_smul c ξ
      map_star' := fun ξ => φ.preTomitaCore_inverse hφ ξ }

end

end CStarAlgebra.ScalarWeight
