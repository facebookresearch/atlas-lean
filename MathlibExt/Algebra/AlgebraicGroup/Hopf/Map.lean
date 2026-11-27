/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/Algebra/AlgebraicGroup/Hopf/Map.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.RingTheory.Bialgebra.Equiv
public import Mathlib.RingTheory.TensorProduct.Maps
public import MathlibExt.Algebra.AlgebraicGroup.FunctorOfPoints

/-!
# Functoriality in the coordinate Hopf algebra

`MathlibExt.Algebra.AlgebraicGroup.FunctorOfPoints` gives the convolution group on
`WithConv (H →ₐ[R] A)`, functorial in the value algebra `A`. This file adds the other
variance needed for the functor-of-points dictionary: a bialgebra morphism
`φ : H₁ →ₐc[R] H₂` induces, by pre-composition, a monoid homomorphism
`WithConv (H₂ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)`.

For a commutative Hopf algebra `H`, this is the contravariant functoriality of
`A ↦ Hom_R(H, A)` in the coordinate Hopf algebra.

## Main declarations

* `BialgHom.mapDomain`: pre-composition by a bialgebra morphism as a monoid homomorphism of
  convolution monoids.
* `BialgHom.mapDomain_injective_of_surjective`: a surjective bialgebra morphism induces an
  injective map on points.
* `BialgHom.mapDomain_id` and `BialgHom.mapDomain_comp`: identity and composition laws.
* `BialgEquiv.mapDomainMulEquiv`: the equiv-version of `BialgHom.mapDomain`, turning a bialgebra
  isomorphism into a multiplicative equivalence of convolution monoids.
* `BialgHom.mapValue_mapDomain`: pre-composition in the coordinate algebra commutes with
  post-composition in the value algebra.
* `BialgHom.mapDomain_inv_apply`: pointwise inverse formula after pre-composition.

The convolution-preservation proof is the bialgebra-morphism version of Mathlib's
`AlgHom.convMul_comp_bialgHom_distrib`, from `Mathlib.RingTheory.Bialgebra.Convolution`.
-/

public section

namespace MathlibExt
namespace AlgHom

open WithConv _root_.AlgHom BialgHom BialgEquiv

variable {R H₁ H₂ H₃ A B : Type*} [CommSemiring R]

section Bialgebra

variable [Semiring H₁] [Semiring H₂]
variable [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]
variable [CommSemiring A] [Algebra R A]

/-- Contravariant functoriality of convolution algebra homomorphisms in the source
bialgebra. A bialgebra morphism `φ : H₁ →ₐc[R] H₂` sends an `A`-valued point of `H₂` to an
`A`-valued point of `H₁` by pre-composition. -/
noncomputable def _root_.BialgHom.mapDomain (φ : H₁ →ₐc[R] H₂) :
    WithConv (H₂ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A) where
  toFun f := toConv (f.ofConv.comp (φ : H₁ →ₐ[R] H₂))
  map_one' := by
    ext x
    simp
  map_mul' f g := by
    apply WithConv.ofConv_injective
    simp [AlgHom.convMul_def, AlgHom.comp_assoc, Algebra.TensorProduct.map_comp]

/-- `mapDomain φ` acts pointwise by pre-composition with `φ`. -/
@[simp]
lemma _root_.BialgHom.mapDomain_apply (φ : H₁ →ₐc[R] H₂)
    (f : WithConv (H₂ →ₐ[R] A)) :
    mapDomain φ f = toConv (f.ofConv.comp (φ : H₁ →ₐ[R] H₂)) := (rfl)

/-- Pointwise form of `mapDomain_apply`. -/
lemma _root_.BialgHom.mapDomain_apply_apply (φ : H₁ →ₐc[R] H₂)
    (f : WithConv (H₂ →ₐ[R] A)) (h : H₁) :
    mapDomain φ f h = f.ofConv (φ h) := (rfl)

/-- Pre-composition by a surjective bialgebra morphism is injective on points. -/
lemma _root_.BialgHom.mapDomain_injective_of_surjective (φ : H₁ →ₐc[R] H₂)
    (hφ : Function.Surjective φ) :
    Function.Injective (mapDomain (A := A) φ) := by
  intro f g hfg
  apply WithConv.ofConv_injective
  apply AlgHom.ext
  intro k
  obtain ⟨h, rfl⟩ := hφ k
  rw [← mapDomain_apply_apply, ← mapDomain_apply_apply, hfg]

end Bialgebra

section BialgebraId

variable [Semiring H₁] [_root_.Bialgebra R H₁]
variable [CommSemiring A] [Algebra R A]

/-- Pre-composition by the identity bialgebra morphism is the identity map on the
convolution monoid. -/
@[simp]
lemma _root_.BialgHom.mapDomain_id :
    (mapDomain (BialgHom.id R H₁) : WithConv (H₁ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)) =
      MonoidHom.id (WithConv (H₁ →ₐ[R] A)) := by
  refine MonoidHom.ext fun f => ?_
  rw [mapDomain_apply, BialgHom.id_toAlgHom, AlgHom.comp_id, toConv_ofConv,
    MonoidHom.id_apply]

end BialgebraId

section BialgebraComp

variable [Semiring H₁] [Semiring H₂] [Semiring H₃]
variable [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂] [_root_.Bialgebra R H₃]
variable [CommSemiring A] [Algebra R A]

/-- Pre-composition by a composite bialgebra morphism is the composite of the corresponding
pre-composition maps. -/
lemma _root_.BialgHom.mapDomain_comp (ψ : H₂ →ₐc[R] H₃) (φ : H₁ →ₐc[R] H₂) :
    (mapDomain (H₁ := H₁) (H₂ := H₃) (ψ.comp φ) :
        WithConv (H₃ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)) =
      (mapDomain (H₁ := H₁) (H₂ := H₂) φ :
          WithConv (H₂ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)).comp
        (mapDomain (H₁ := H₂) (H₂ := H₃) ψ :
          WithConv (H₃ →ₐ[R] A) →* WithConv (H₂ →ₐ[R] A)) := by
  refine MonoidHom.ext fun f => ?_
  rw [MonoidHom.comp_apply, mapDomain_apply, mapDomain_apply, mapDomain_apply,
    toConv_ofConv, BialgHom.comp_toAlgHom, AlgHom.comp_assoc]

end BialgebraComp

section BialgebraEquiv

variable [Semiring H₁] [Semiring H₂]
variable [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]
variable [CommSemiring A] [Algebra R A]

/-- A bialgebra isomorphism `e : H₁ ≃ₐc[R] H₂` induces a multiplicative equivalence of the
convolution monoids of points, by pre-composition: the equiv-version of the contravariant
functoriality `mapDomain`. -/
noncomputable def _root_.BialgEquiv.mapDomainMulEquiv (e : H₁ ≃ₐc[R] H₂) :
    WithConv (H₂ →ₐ[R] A) ≃* WithConv (H₁ →ₐ[R] A) where
  toFun := mapDomain (A := A) (e : H₁ →ₐc[R] H₂)
  invFun := mapDomain (A := A) (e.symm : H₂ →ₐc[R] H₁)
  map_mul' := map_mul _
  left_inv f := by
    have h : (mapDomain (A := A) (e.symm : H₂ →ₐc[R] H₁)).comp
        (mapDomain (A := A) (e : H₁ →ₐc[R] H₂)) = MonoidHom.id _ := by
      rw [← mapDomain_comp, e.comp_symm, mapDomain_id]
    exact DFunLike.congr_fun h f
  right_inv f := by
    have h : (mapDomain (A := A) (e : H₁ →ₐc[R] H₂)).comp
        (mapDomain (A := A) (e.symm : H₂ →ₐc[R] H₁)) = MonoidHom.id _ := by
      rw [← mapDomain_comp, e.symm_comp, mapDomain_id]
    exact DFunLike.congr_fun h f

/-- `mapDomainMulEquiv` acts by the underlying `mapDomain` in the forward direction. -/
@[simp]
lemma _root_.BialgEquiv.mapDomainMulEquiv_apply (e : H₁ ≃ₐc[R] H₂)
    (f : WithConv (H₂ →ₐ[R] A)) :
    mapDomainMulEquiv e f = mapDomain (e : H₁ →ₐc[R] H₂) f := (rfl)

/-- `mapDomainMulEquiv` acts by pre-composition with the inverse bialgebra equivalence in the
reverse direction. -/
@[simp]
lemma _root_.BialgEquiv.mapDomainMulEquiv_symm_apply (e : H₁ ≃ₐc[R] H₂)
    (f : WithConv (H₁ →ₐ[R] A)) :
    (mapDomainMulEquiv (A := A) e).symm f = mapDomain (e.symm : H₂ →ₐc[R] H₁) f := (rfl)

end BialgebraEquiv

section BialgebraMapValue

variable [Semiring H₁] [Semiring H₂] [_root_.Bialgebra R H₁] [_root_.Bialgebra R H₂]
variable [CommSemiring A] [Algebra R A]
variable [CommSemiring B] [Algebra R B]

/-- Pre-composition in the coordinate bialgebra commutes with post-composition in the value
algebra. -/
lemma _root_.BialgHom.mapValue_mapDomain (φ : H₁ →ₐc[R] H₂) (χ : A →ₐ[R] B) :
    (mapDomain (H₁ := H₁) (H₂ := H₂) φ :
        WithConv (H₂ →ₐ[R] B) →* WithConv (H₁ →ₐ[R] B)).comp
        (AlgHom.mapValue (H := H₂) χ) =
      (AlgHom.mapValue (H := H₁) χ).comp
        (mapDomain (H₁ := H₁) (H₂ := H₂) φ :
          WithConv (H₂ →ₐ[R] A) →* WithConv (H₁ →ₐ[R] A)) := by
  refine MonoidHom.ext fun f => ?_
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, mapDomain_apply, AlgHom.mapValue_apply,
    mapDomain_apply, AlgHom.mapValue_apply, toConv_ofConv, toConv_ofConv, AlgHom.comp_assoc]

end BialgebraMapValue

section Hopf

variable [Semiring H₁] [Semiring H₂]
variable [_root_.Bialgebra R H₁] [_root_.HopfAlgebra R H₂]
variable [CommSemiring A] [Algebra R A]

/-- Pre-composition of the convolution inverse evaluates the original point at the antipode
of the bialgebra morphism's value. When `H₁` is also a Hopf algebra, preservation of inverses
follows from `mapDomain` being a `MonoidHom`. -/
lemma _root_.BialgHom.mapDomain_inv_apply (φ : H₁ →ₐc[R] H₂) (f : WithConv (H₂ →ₐ[R] A)) (h : H₁) :
    mapDomain (H₁ := H₁) (H₂ := H₂) φ (f⁻¹ : WithConv (H₂ →ₐ[R] A)) h =
      f.ofConv (HopfAlgebra.antipode R (φ h)) := by
  rw [mapDomain_apply_apply]
  exact algHom_inv_apply f (φ h)

end Hopf

end AlgHom
end MathlibExt
