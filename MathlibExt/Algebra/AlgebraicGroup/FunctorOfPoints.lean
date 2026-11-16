/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/

/-
Source port of TauCeti/Algebra/AlgebraicGroup/FunctorOfPoints.lean.
TauCeti revision 62bbc0596dc3539d488232e4e924a338548ea0a9.
Modifications: change only project namespaces and import paths.
The original Apache 2.0 copyright and authors above are retained.
-/
module

public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# Convolution groups of algebra homomorphisms out of a Hopf algebra

For an arbitrary Hopf algebra `H` over `R` and a commutative `R`-algebra `A`, the convolution
monoid of `R`-algebra homomorphisms `H →ₐ[R] A` is a **group**, with inverse `f ↦ f ∘ S`,
where `S` is the antipode of `H`. The source `H` need only be a Hopf algebra; it is *not*
required to be commutative.

Mathlib already constructs the convolution `Monoid` on `WithConv (H →ₐ[R] A)` for `H` a
bialgebra (`Mathlib/RingTheory/Bialgebra/Convolution.lean`): multiplication is the
convolution product `(f * g)(h) = ∑ f(h₍₁₎) * g(h₍₂₎)` and the unit is
`algebraMap ∘ ε`.
What is added here is the **inverse** and hence the **group** structure, available exactly
when `H` carries an antipode `S`: the inverse of `f` is `f ∘ S`.
Mathlib's `AlgHom.convInv` and `AlgHom.convGroup` additionally assume that the source is
commutative and the value algebra is a bialgebra; the constructions here remove those requirements.

The construction is functorial in the value algebra: post-composition with an `R`-algebra
homomorphism `φ : A →ₐ[R] B` gives a monoid homomorphism `mapValue φ` between the convolution
monoids, preserving identities and composition. This part needs only the bialgebra structure
on `H` (the convolution monoid), so it lives in its own `Bialgebra` section.

## Application: affine group schemes

When `H` is moreover *commutative*, `Spec H` is an affine group scheme, and the above is
the group structure on its functor of points `A ↦ (H →ₐ[R] A)`, with functoriality in
`A` realizing the `R-Alg ⥤ Grp` structure, where the counit is the identity and `f ∘ S` is
the inverse.

## Main results

* `WithConv.algHom_inv_apply`: pointwise, the convolution inverse of `f` sends `h` to `f (S h)`.
* `AlgHom.convGroupOfSemiring`, `AlgHom.convCommGroupOfSemiring`: for `H` a Hopf algebra over `R`
  and `A` a commutative `R`-algebra, `WithConv (H →ₐ[R] A)` is a group, commutative when `H`
  is cocommutative.
* `AlgHom.mapValue`: post-composition with `φ : A →ₐ[R] B` as a monoid homomorphism of
  convolution monoids, with `AlgHom.ofConv_comp_mapValue` describing it on underlying
  homomorphisms, `AlgHom.mapValue_id`, `AlgHom.mapValue_comp` recording its
  functoriality in the value algebra and `AlgHom.mapValue_injective` recording that it loses no
  information when `φ` does not.
* `WithConv.mapValue_algebraOfId`: mapping a base-valued point through an algebra-valued point
  gives the corresponding constant point.

## References

The convolution monoid on algebra homomorphisms builds on Mathlib's convolution monoid of
Yaël Dillies and Michał Mrugała, and the Hopf convolution algebra developed by
Yaël Dillies, Michał Mrugała, and Yunzhou Xie.
-/

public section

open _root_.Coalgebra HopfAlgebra TensorProduct WithConv

namespace AlgHom

variable {R H A : Type*} [CommSemiring R]

section Hopf

variable [Semiring H] [_root_.HopfAlgebra R H] [CommSemiring A] [Algebra R A]

/-- Precomposition of an algebra homomorphism `f : H →ₐ[R] A` with the antipode `S` of
`H`, as an `R`-algebra homomorphism `H →ₐ[R] A`. Its underlying linear map is
`f.toLinearMap ∘ₗ HopfAlgebra.antipode R`. This is well-defined even when `H` is
noncommutative: `S` is an antihomomorphism (`HopfAlgebra.antipode_mul_antidistrib`), and `A` is
commutative, so `f ∘ S` is a homomorphism. The construction composes
`HopfAlgebra.antipodeAlgHomOp` with `AlgHom.fromOpposite`. -/
noncomputable def antipodeComp (f : H →ₐ[R] A) : H →ₐ[R] A :=
  (f.fromOpposite fun x y => Commute.all (f x) (f y)).comp (HopfAlgebra.antipodeAlgHomOp R H)

/-- Evaluation of `antipodeComp f` at an element `h : H` is `f (S h)`. -/
@[simp]
lemma antipodeComp_apply (f : H →ₐ[R] A) (h : H) :
    antipodeComp f h = f (antipode R h) := by
  delta antipodeComp
  rfl

/-- The underlying linear map of `antipodeComp f` is `f.toLinearMap ∘ₗ antipode R`. -/
@[simp]
lemma toLinearMap_antipodeComp (f : H →ₐ[R] A) :
    (antipodeComp f).toLinearMap = f.toLinearMap ∘ₗ antipode R := by
  delta antipodeComp
  rfl

/-- The convolution inverse of an `R`-algebra homomorphism `f : H →ₐ[R] A` out of a Hopf
algebra is `f ∘ S`, where `S` is the antipode. The source need only be a semiring, so it can be
noncommutative, and the value semiring needs only an `R`-algebra structure. -/
noncomputable instance convInvOfSemiring : Inv (WithConv (H →ₐ[R] A)) where
  inv f := toConv (antipodeComp f.ofConv)

/-- The convolution inverse of `f` is `f ∘ S`, where `S` is the antipode:
`f⁻¹ = toConv (antipodeComp f.ofConv)`. -/
lemma _root_.WithConv.algHom_inv_def (f : WithConv (H →ₐ[R] A)) :
    f⁻¹ = toConv (antipodeComp f.ofConv) := rfl

/-- Pointwise, the convolution inverse of `f` sends `h` to `f (S h)`, where `S` is the
antipode. -/
@[simp]
lemma _root_.WithConv.algHom_inv_apply (f : WithConv (H →ₐ[R] A)) (h : H) :
    f⁻¹ h = f.ofConv (antipode R h) := by
  -- `algHom_inv_def` exposes `toConv (antipodeComp f.ofConv)`; under the coercion from `WithConv`,
  -- `(toConv g) h` evaluates as `g h`.
  rw [WithConv.algHom_inv_def, AlgHom.antipodeComp_apply]

/-- For a Hopf algebra `H` over `R` and a commutative `R`-algebra `A`, the convolution
monoid of `R`-algebra homomorphisms `H →ₐ[R] A` is a group, with inverse `f ↦ f ∘ S`. When
`H` is moreover commutative, `Spec H` is an affine group scheme and this is the group
structure on its functor of points evaluated at `A`. -/
noncomputable instance convGroupOfSemiring : Group (WithConv (H →ₐ[R] A)) where
  inv_mul_cancel f := by
    -- Pass to linear maps to use the Sweedler formula for convolution.
    refine WithConv.ofConv_injective (AlgHom.toLinearMap_injective (WithConv.toConv_injective ?_))
    rw [AlgHom.toLinearMap_convMul, AlgHom.toLinearMap_convOne, algHom_inv_def, toConv_ofConv,
      AlgHom.toLinearMap_antipodeComp]
    ext h
    rw [(ℛ R h).convMul_apply]
    simp only [LinearMap.comp_apply, AlgHom.coe_toLinearMap, LinearMap.convOne_apply,
      ← map_mul, ← map_sum, sum_antipode_mul_eq_algebraMap_counit, AlgHom.commutes]

end Hopf

section Bialgebra

variable [Semiring H] [_root_.Bialgebra R H] [CommSemiring A] [Algebra R A]
variable {B : Type*} [CommSemiring B] [Algebra R B]

/-- Functoriality of `A ↦ (H →ₐ[R] A)` in the value algebra: an `R`-algebra homomorphism
`φ : A →ₐ[R] B` induces, by post-composition, a monoid homomorphism between the convolution
monoids. This needs only the bialgebra structure on `H`. When `H` is moreover a Hopf algebra,
these convolution monoids are the convolution groups (`convGroupOfSemiring`); a `MonoidHom`
between groups is automatically a group homomorphism, so no separate construction is needed
there. -/
noncomputable def mapValue (φ : A →ₐ[R] B) :
    WithConv (H →ₐ[R] A) →* WithConv (H →ₐ[R] B) where
  toFun f := toConv (φ.comp f.ofConv)
  map_one' := by
    rw [AlgHom.convOne_def, toConv_ofConv, ← AlgHom.comp_assoc, Algebra.comp_ofId,
      AlgHom.convOne_def]
  map_mul' f g := by
    rw [toConv_ofConv, toConv_ofConv, AlgHom.comp_convMul_distrib, toConv_ofConv, toConv_ofConv]

/-- `mapValue φ` acts pointwise by post-composition: `(mapValue φ f) = φ ∘ f`. -/
@[simp]
lemma mapValue_apply (φ : A →ₐ[R] B) (f : WithConv (H →ₐ[R] A)) :
    mapValue φ f = toConv (φ.comp f.ofConv) := by
  delta mapValue
  rfl

/-- On underlying homomorphisms, `mapValue φ` is post-composition with `φ`, as functions. -/
lemma ofConv_comp_mapValue (φ : A →ₐ[R] B) :
    ofConv ∘ mapValue (H := H) φ = (fun f : H →ₐ[R] A ↦ φ.comp f) ∘ ofConv := by
  ext f h
  simp

/-- `mapValue` preserves the identity: `mapValue (𝟙 A)` is the identity monoid homomorphism. -/
@[simp]
lemma mapValue_id :
    mapValue (H := H) (AlgHom.id R A) = MonoidHom.id (WithConv (H →ₐ[R] A)) := by
  refine MonoidHom.ext fun f => ?_
  rw [mapValue_apply, AlgHom.id_comp, toConv_ofConv, MonoidHom.id_apply]

/-- An injective homomorphism of value algebras induces an injective map on points: a point is
determined by its values. -/
lemma mapValue_injective {φ : A →ₐ[R] B} (hφ : Function.Injective φ) :
    Function.Injective (mapValue (H := H) φ) := by
  intro f g hfg
  rw [mapValue_apply, mapValue_apply] at hfg
  refine WithConv.ofConv_injective (AlgHom.ext fun h => hφ ?_)
  exact DFunLike.congr_fun (WithConv.toConv_injective hfg) h

/-- For an injective homomorphism `φ` of value algebras, a point comes from a point valued in the
source of `φ` exactly when each of its values lies in the range of `φ`. -/
lemma mem_mrange_mapValue_iff {φ : A →ₐ[R] B} (hφ : Function.Injective φ)
    {f : WithConv (H →ₐ[R] B)} :
    f ∈ MonoidHom.mrange (mapValue (H := H) φ) ↔ ∀ h, f.ofConv h ∈ φ.range := by
  refine ⟨?_, fun hf => ?_⟩
  · rintro ⟨g, rfl⟩ h
    rw [mapValue_apply, ofConv_toConv]
    exact φ.mem_range_self _
  · -- The values lie in the range of `φ`; invert `φ` there.
    refine ⟨toConv ((AlgEquiv.ofInjective φ hφ).symm.toAlgHom.comp (f.ofConv.codRestrict _ hf)),
      WithConv.ofConv_injective (AlgHom.ext fun h => ?_)⟩
    rw [mapValue_apply, ofConv_toConv, ofConv_toConv, AlgHom.comp_apply, AlgHom.comp_apply,
      AlgEquiv.coe_toAlgHom, ← AlgEquiv.ofInjective_apply _ hφ, AlgEquiv.apply_symm_apply,
      AlgHom.coe_codRestrict]

variable {C : Type*} [CommSemiring C] [Algebra R C]

/-- `mapValue` preserves composition: `mapValue (ψ ∘ φ) = mapValue ψ ∘ mapValue φ`. -/
lemma mapValue_comp (ψ : B →ₐ[R] C) (φ : A →ₐ[R] B) :
    mapValue (H := H) (ψ.comp φ) = (mapValue ψ).comp (mapValue φ) := by
  refine MonoidHom.ext fun f => ?_
  rw [MonoidHom.comp_apply, mapValue_apply, mapValue_apply, mapValue_apply, toConv_ofConv,
    AlgHom.comp_assoc]

end Bialgebra

section BialgebraConstantPoint

variable {R H₁ A : Type*} [CommSemiring R] [CommSemiring H₁] [_root_.Bialgebra R H₁]
variable [CommSemiring A] [Algebra R A]

/-- Mapping a base-valued point first to the coordinate algebra and then through an
algebra-valued point gives the corresponding constant point in the value algebra. -/
lemma _root_.WithConv.mapValue_algebraOfId (x : WithConv (H₁ →ₐ[R] A))
    (g : WithConv (H₁ →ₐ[R] R)) :
    mapValue (H := H₁) x.ofConv
        (mapValue (H := H₁) (Algebra.ofId R H₁) g) =
      mapValue (H := H₁) (Algebra.ofId R A) g := by
  have h := DFunLike.congr_fun
    (mapValue_comp (H := H₁) x.ofConv (Algebra.ofId R H₁)) g
  simpa [Algebra.comp_ofId] using h.symm

end BialgebraConstantPoint

section CommHopf

variable [Semiring H] [_root_.HopfAlgebra R H] [IsCocomm R H] [CommSemiring A] [Algebra R A]

/-- When `H` is moreover cocommutative, the convolution group of `R`-algebra homomorphisms
`H →ₐ[R] A` is abelian. -/
noncomputable instance convCommGroupOfSemiring : CommGroup (WithConv (H →ₐ[R] A)) where
  mul_comm := mul_comm

end CommHopf

end AlgHom
