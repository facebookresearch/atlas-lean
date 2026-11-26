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

public import MathlibExt.Algebra.Category.ModuleCat.ExtendedRestrictedQuotient

/-!
# Base change of quotient-ring module presentations

Let φ : R → A and ψ : S → B be surjective maps of commutative rings, and let γ : R → S send
ker(φ) onto ker(ψ) as an extended ideal. Then S ⊗_R A is canonically isomorphic to B as an
S-module through its quotient presentation.

If δ : A → B satisfies δφ = ψγ, the comparison sends s ⊗ a to ψ(s)δ(a). The induced R-linear
restriction map sends a to δ(a). These comparisons compose through a second base-change
square, with the canonical scalar-extension associativity isomorphism included.
-/

public section
noncomputable section
set_option autoImplicit false

open CategoryTheory
open scoped TensorProduct ChangeOfRings

namespace ModuleCat

universe u

variable (R S A B : Type u) [CommRing R] [CommRing S] [CommRing A] [CommRing B]
variable (φ : R →+* A) (ψ : S →+* B) (γ : R →+* S)
variable (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ)
variable (hk : (RingHom.ker φ).map γ = RingHom.ker ψ)

/-- The base-change isomorphism of surjective scalar presentations.

For surjective φ and ψ with γ(ker φ) generating ker ψ, identify the scalar extension S ⊗_R A
with B restricted along ψ, through the quotient-module presentations. -/
def surjectiveScalarBaseChangeIso :
    (extendScalars γ).obj ((restrictScalars φ).obj (ModuleCat.of A A)) ≅
      (restrictScalars ψ).obj (ModuleCat.of B B) := by
  let : Algebra R S := γ.toAlgebra
  let eA := surjectiveQuotientModuleIso R A φ hφ
  let eB := surjectiveQuotientModuleIso S B ψ hψ
  let e₁ := (extendScalars γ).mapIso eA.symm
  let e₂ : (extendScalars γ).obj (ModuleCat.of R (R ⧸ RingHom.ker φ)) ≅
      ModuleCat.of S (S ⧸ (RingHom.ker φ).map γ) :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (RingHom.ker φ)).symm.toLinearEquiv.toModuleIso
  let e₃ := (Ideal.quotientEquivAlgOfEq S hk).toLinearEquiv.toModuleIso
  exact e₁ ≪≫ e₂ ≪≫ e₃ ≪≫ eB

/-- The quotient base-change comparison on a scalar image.

For s ∈ S and r ∈ R, the comparison sends s ⊗ φ(r) to ψ(γ(r)s). -/
theorem surjectiveScalarBaseChangeIso_hom_tmul_image (s : S) (r : R) :
    (surjectiveScalarBaseChangeIso R S A B φ ψ γ hφ hψ hk).hom (s ⊗ₜ[R, γ] φ r) =
      ψ (γ r * s) := by
  let : Algebra R S := γ.toAlgebra
  let eA := surjectiveQuotientModuleIso R A φ hφ
  let eB := surjectiveQuotientModuleIso S B ψ hψ
  let e₂ := (Algebra.TensorProduct.quotIdealMapEquivTensorQuot S (RingHom.ker φ)).symm
  let e₃ := Ideal.quotientEquivAlgOfEq S hk
  have hm : (extendScalars γ).map eA.inv (s ⊗ₜ[R, γ] φ r) =
      s ⊗ₜ[R, γ] Ideal.Quotient.mk (RingHom.ker φ) r := by
    have h := ExtendScalars.map_tmul γ eA.inv s (φ r)
    rw [surjectiveQuotientModuleIso_inv_map] at h
    exact h
  have hq : e₂ (s ⊗ₜ[R] Ideal.Quotient.mk (RingHom.ker φ) r) =
      Ideal.Quotient.mk ((RingHom.ker φ).map γ) (γ r * s) :=
    Algebra.TensorProduct.quotIdealMapEquivTensorQuot_symm_tmul S (RingHom.ker φ) s r
  have he : e₃ (Ideal.Quotient.mk ((RingHom.ker φ).map γ) (γ r * s)) =
      Ideal.Quotient.mk (RingHom.ker ψ) (γ r * s) :=
    Ideal.quotientEquivAlgOfEq_mk S hk (γ r * s)
  change eB.hom (e₃ (e₂ ((extendScalars γ).map eA.inv (s ⊗ₜ[R, γ] φ r)))) = _
  exact (congrArg (fun x => eB.hom (e₃ (e₂ x))) hm).trans
    ((congrArg (fun x => eB.hom (e₃ x)) hq).trans
      ((congrArg (fun x => eB.hom x) he).trans
        (surjectiveQuotientModuleIso_hom_mk S B ψ hψ (γ r * s))))

/-- The quotient base-change comparison on every pure tensor.

If δφ = ψγ, the comparison sends s ⊗ a to ψ(s)δ(a). -/
theorem surjectiveScalarBaseChangeIso_hom_tmul
    (δ : A →+* B) (hδ : δ.comp φ = ψ.comp γ) (s : S) (a : A) :
    (surjectiveScalarBaseChangeIso R S A B φ ψ γ hφ hψ hk).hom (s ⊗ₜ[R, γ] a) =
      ψ s * δ a := by
  obtain ⟨r, rfl⟩ := hφ a
  rw [surjectiveScalarBaseChangeIso_hom_tmul_image, map_mul, mul_comm]
  exact congrArg (fun b => ψ s * b) (congrArg (fun f : R →+* B => f r) hδ).symm

/-- The induced restriction map between quotient coefficients.

Compose the scalar-extension unit A → res_γ(S ⊗_R A) with the restricted base-change
comparison to obtain the R-linear map from A to B with the specified scalar actions. -/
def surjectiveScalarRestrictionMap :
    (restrictScalars φ).obj (ModuleCat.of A A) ⟶
      (restrictScalars γ).obj ((restrictScalars ψ).obj (ModuleCat.of B B)) :=
  (extendRestrictScalarsAdj γ).unit.app _ ≫
    (restrictScalars γ).map (surjectiveScalarBaseChangeIso R S A B φ ψ γ hφ hψ hk).hom

/-- Values of the quotient-coefficient restriction map.

For a compatible ring map δ : A → B, the induced restriction map sends a to δ(a). -/
theorem surjectiveScalarRestrictionMap_apply
    (δ : A →+* B) (hδ : δ.comp φ = ψ.comp γ) (a : A) :
    surjectiveScalarRestrictionMap R S A B φ ψ γ hφ hψ hk a = δ a := by
  unfold surjectiveScalarRestrictionMap
  erw [ConcreteCategory.comp_apply, extendRestrictScalarsAdj_unit_app_apply,
    restrictScalars.map_apply, surjectiveScalarBaseChangeIso_hom_tmul R S A B φ ψ γ hφ hψ hk δ hδ,
    map_one, one_mul]

end ModuleCat

namespace ModuleCat

universe u

/-- Composition of quotient base-change comparisons.

For two consecutive scalar maps and compatible surjective presentations, extending the first
comparison and then applying the second equals the comparison for the composite, after the
canonical scalar-extension comparison. -/
theorem surjectiveScalarBaseChangeIso_hom_trans
    (R S T A B C : Type u) [CommRing R] [CommRing S] [CommRing T]
    [CommRing A] [CommRing B] [CommRing C]
    (φ : R →+* A) (ψ : S →+* B) (χ : T →+* C)
    (γ : R →+* S) (ε : S →+* T) (δ : A →+* B) (ζ : B →+* C)
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ) (hχ : Function.Surjective χ)
    (hk₁ : (RingHom.ker φ).map γ = RingHom.ker ψ)
    (hk₂ : (RingHom.ker ψ).map ε = RingHom.ker χ)
    (hδ : δ.comp φ = ψ.comp γ) (hζ : ζ.comp ψ = χ.comp ε) :
    (extendScalarsComp γ ε).hom.app ((restrictScalars φ).obj (ModuleCat.of A A)) ≫
      (extendScalars ε).map (surjectiveScalarBaseChangeIso R S A B φ ψ γ hφ hψ hk₁).hom ≫
        (surjectiveScalarBaseChangeIso S T B C ψ χ ε hψ hχ hk₂).hom =
      (surjectiveScalarBaseChangeIso R T A C φ χ (ε.comp γ) hφ hχ
        (by rw [← Ideal.map_map, hk₁, hk₂])).hom := by
  have hcomp : (ζ.comp δ).comp φ = χ.comp (ε.comp γ) := by
    rw [RingHom.comp_assoc, hδ, ← RingHom.comp_assoc, hζ, RingHom.comp_assoc]
  let J : ModuleCat R := (restrictScalars φ).obj (ModuleCat.of A A)
  let e₁ := surjectiveScalarBaseChangeIso R S A B φ ψ γ hφ hψ hk₁
  let e₂ := surjectiveScalarBaseChangeIso S T B C ψ χ ε hψ hχ hk₂
  let e₃ := surjectiveScalarBaseChangeIso R T A C φ χ (ε.comp γ) hφ hχ
    (by rw [← Ideal.map_map, hk₁, hk₂])
  let : Algebra R S := γ.toAlgebra
  let : Algebra S T := ε.toAlgebra
  let : Algebra R T := (ε.comp γ).toAlgebra
  let : Algebra R A := φ.toAlgebra
  let K := (extendScalars (ε.comp γ)).obj J
  let N := (restrictScalars χ).obj (ModuleCat.of C C)
  let : Module R K := Module.compHom K (ε.comp γ)
  let : Module R N := Module.compHom N (ε.comp γ)
  let : IsScalarTower R T K := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let : IsScalarTower R T N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let f := ((extendScalarsComp γ ε).hom.app J ≫ (extendScalars ε).map e₁.hom ≫ e₂.hom).hom
  let g := e₃.hom.hom
  apply ModuleCat.hom_ext
  change f = g
  apply LinearMap.restrictScalars_injective R
  apply TensorProduct.ext'
  intro t a
  change T at t
  change A at a
  have hu := extendScalarsComp_hom_app_one_tmul γ ε J a
  have ht : (extendScalarsComp γ ε).hom.app J (t ⊗ₜ[R, ε.comp γ] a) =
      t ⊗ₜ[S, ε] ((1 : S) ⊗ₜ[R, γ] a) := by
    have h := ((extendScalarsComp γ ε).hom.app J).hom.map_smul t
      ((1 : T) ⊗ₜ[R, ε.comp γ] a)
    have hs := congrArg (fun m : (extendScalars ε).obj ((extendScalars γ).obj J) => t • m) hu
    have h₁ : t • ((1 : T) ⊗ₜ[R, ε.comp γ] a) = t ⊗ₜ[R, ε.comp γ] a := by
      change (t : T) • ((1 : T) ⊗ₜ[R] a) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    have h₂ : t • ((1 : T) ⊗ₜ[S, ε] ((1 : S) ⊗ₜ[R, γ] a)) =
        t ⊗ₜ[S, ε] ((1 : S) ⊗ₜ[R, γ] a) := by
      change (t : T) • ((1 : T) ⊗ₜ[S] ((1 : S) ⊗ₜ[R] a)) = _
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    exact ((congrArg (fun m => ((extendScalarsComp γ ε).hom.app J) m) h₁).symm.trans
      (h.trans hs)).trans h₂
  change e₂.hom ((extendScalars ε).map e₁.hom
      ((extendScalarsComp γ ε).hom.app J (t ⊗ₜ[R, ε.comp γ] a))) = e₃.hom (t ⊗ₜ[R, ε.comp γ] a)
  rw [ht]
  have hm := ExtendScalars.map_tmul ε e₁.hom t ((1 : S) ⊗ₜ[R, γ] a)
  erw [hm]
  erw [surjectiveScalarBaseChangeIso_hom_tmul R S A B φ ψ γ hφ hψ hk₁ δ hδ,
    map_one, one_mul,
    surjectiveScalarBaseChangeIso_hom_tmul S T B C ψ χ ε hψ hχ hk₂ ζ hζ,
    surjectiveScalarBaseChangeIso_hom_tmul R T A C φ χ (ε.comp γ) hφ hχ
      (by rw [← Ideal.map_map, hk₁, hk₂]) (ζ.comp δ) hcomp]
  rfl

end ModuleCat

namespace ModuleCat

universe u

/-- Composition of induced quotient-coefficient restriction maps.

For two compatible base-change squares, applying the two induced restriction maps successively
equals the restriction map of the composite square on every a ∈ A. -/
theorem surjectiveScalarRestrictionMap_trans
    (R S T A B C : Type u) [CommRing R] [CommRing S] [CommRing T]
    [CommRing A] [CommRing B] [CommRing C]
    (φ : R →+* A) (ψ : S →+* B) (χ : T →+* C)
    (γ : R →+* S) (ε : S →+* T) (δ : A →+* B) (ζ : B →+* C)
    (hφ : Function.Surjective φ) (hψ : Function.Surjective ψ) (hχ : Function.Surjective χ)
    (hk₁ : (RingHom.ker φ).map γ = RingHom.ker ψ)
    (hk₂ : (RingHom.ker ψ).map ε = RingHom.ker χ)
    (hδ : δ.comp φ = ψ.comp γ) (hζ : ζ.comp ψ = χ.comp ε) (a : A) :
    surjectiveScalarRestrictionMap S T B C ψ χ ε hψ hχ hk₂
        (surjectiveScalarRestrictionMap R S A B φ ψ γ hφ hψ hk₁ a) =
      surjectiveScalarRestrictionMap R T A C φ χ (ε.comp γ) hφ hχ
        (by rw [← Ideal.map_map, hk₁, hk₂]) a := by
  have hcomp : (ζ.comp δ).comp φ = χ.comp (ε.comp γ) := by
    rw [RingHom.comp_assoc, hδ, ← RingHom.comp_assoc, hζ, RingHom.comp_assoc]
  rw [surjectiveScalarRestrictionMap_apply R S A B φ ψ γ hφ hψ hk₁ δ hδ,
    surjectiveScalarRestrictionMap_apply S T B C ψ χ ε hψ hχ hk₂ ζ hζ,
    surjectiveScalarRestrictionMap_apply R T A C φ χ (ε.comp γ) hφ hχ
      (by rw [← Ideal.map_map, hk₁, hk₂]) (ζ.comp δ) hcomp]
  rfl

end ModuleCat
