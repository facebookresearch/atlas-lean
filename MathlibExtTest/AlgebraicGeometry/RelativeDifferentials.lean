/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicGeometry.RelativeDifferentials
public import Mathlib.Algebra.Polynomial.Basic
public import Mathlib.RingTheory.Smooth.StandardSmooth

/-!
# Tests for the sheaf of relative differentials
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

#check @AlgebraicGeometry.Scheme.constToPresheaf
#check @AlgebraicGeometry.Scheme.relativeDifferentialsPresheaf
#check @AlgebraicGeometry.Scheme.relativeDifferentials
#check @AlgebraicGeometry.Scheme.Modules.presheafOfModulesOfCommRing
#check @AlgebraicGeometry.Scheme.relativeDifferentialsPresheafHomEquiv
#check @AlgebraicGeometry.Scheme.relativeDifferentialsHomEquiv
#check @AlgebraicGeometry.Scheme.relativeDifferentialsDerivation
#check @AlgebraicGeometry.Scheme.relativeDifferentialsSpecIso
#check @AlgebraicGeometry.Scheme.relativeDifferentialsSpecΓIso
#check @AlgebraicGeometry.Scheme.relativeDifferentialsSpecΓIso_hom_d
#check @AlgebraicGeometry.Scheme.isQuasicoherent_relativeDifferentials_Spec
#check @AlgebraicGeometry.Scheme.relativeDifferentialsSpecIsoFree
#check @AlgebraicGeometry.Scheme.relativeDifferentialsSpecIsoUnit
#check @AlgebraicGeometry.Scheme.exists_iso_free_of_isStandardSmoothOfRelativeDimension
#check @KaehlerDifferential.LocalizationAux.liftOfLocalization
#check @KaehlerDifferential.LocalizationAux.liftOfLocalization_bijective
#check @KaehlerDifferential.LocalizationAux.dOfLocalization
#check @KaehlerDifferential.LocalizationAux.dOfLocalization_naturality

/-- The affine line over `ℤ`: `Γ(𝔸¹_ℤ, Ω_{𝔸¹/ℤ}) ≅ Ω[ℤ[X]⁄ℤ]`. -/
noncomputable example :
    let f : CommRingCat.of ℤ ⟶ CommRingCat.of (Polynomial ℤ) :=
      CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ))
    moduleSpecΓFunctor.obj (relativeDifferentials (f ≫ (ΓSpecIso _).inv)) ≅
      CommRingCat.KaehlerDifferential f :=
  relativeDifferentialsSpecΓIso _

/-- The sheaf of relative differentials of `Spec ℤ[X]` over `ℤ` is quasi-coherent. -/
example :
    (relativeDifferentials (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ)) ≫
      (ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv)).IsQuasicoherent :=
  inferInstance

/-- On `Spec ℤ[X]` over `ℤ`, the global-sections isomorphism sends the universal derivation of
`X` to `d X`. -/
example :
    (relativeDifferentialsSpecΓIso (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ)))).hom
      ((relativeDifferentialsDerivation (CommRingCat.ofHom (algebraMap ℤ (Polynomial ℤ)) ≫
        (ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv)).d (X := .op ⊤)
          ((ΓSpecIso (CommRingCat.of (Polynomial ℤ))).inv Polynomial.X)) =
      CommRingCat.KaehlerDifferential.d Polynomial.X :=
  relativeDifferentialsSpecΓIso_hom_d _ _

/-- Over any scheme, morphisms out of `Ω_{X/R}` are derivations. -/
noncomputable example (R : CommRingCat) (X : Scheme) (φ : R ⟶ Γ(X, ⊤)) (F : X.Modules) :
    (relativeDifferentials φ ⟶ F) ≃
      F.presheafOfModulesOfCommRing.Derivation' (constToPresheaf φ) :=
  relativeDifferentialsHomEquiv φ F

/-- The affine line `Spec ℤ[X]` over `ℤ`: its sheaf of relative differentials is free on a set
with one element. -/
example : ∃ ι : Type, Cardinal.mk ι = 1 ∧
    Nonempty (relativeDifferentials
      (CommRingCat.ofHom (algebraMap ℤ (MvPolynomial (Fin 1) ℤ)) ≫
        (ΓSpecIso (CommRingCat.of (MvPolynomial (Fin 1) ℤ))).inv) ≅ SheafOfModules.free ι) :=
  exists_iso_free_of_isStandardSmoothOfRelativeDimension _ 1
    (cast (congrArg (fun i => @Algebra.IsStandardSmoothOfRelativeDimension 1 ℤ
      (MvPolynomial (Fin 1) ℤ) _ _ i) (Subsingleton.elim _ _)) inferInstance)
