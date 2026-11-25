/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Algebra.Category.ModuleCat.SimplicialCoefficientFamilies
public import MathlibExt.AlgebraicTopology.DoldKan.AdditiveNormalization
public import Mathlib.Algebra.Category.ModuleCat.Ulift

/-!
# Returning native lifted coefficients to the original normalized tensor model

The original coefficient carrier and original diagram carrier have
independent worlds. The native tensor congruence with coefficient down,
followed by native output up, compares the lifted-coefficient tensor with
the lifted original tensor. Its generator formula retains the original
linear-map values. Native additive normalization then compares the same
normalized models; no Small/Flat premise or new coefficient category is
needed.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v s t h

namespace ModuleCat.SimplicialCoefficientLift

variable (R : Type u) [CommRing R]

/-- The actual tensor of native lifted coefficients returns to the native lift of the original tensor. -/
def tensorIso (M : ModuleCat.{s} R) (X : ModuleCat.{v} R) :
    tensorObjAt R ((uliftFunctor.{h, s} R).obj M) X ≅
      (uliftFunctor.{h, max v s} R).obj (tensorObjAt R M X) :=
  ((TensorProduct.congr (ULift.moduleEquiv : ULift.{h} M ≃ₗ[R] M)
      (LinearEquiv.refl R X)).trans
    (ULift.moduleEquiv : ULift.{h} (M ⊗[R] X) ≃ₗ[R] M ⊗[R] X).symm).toModuleIso

/-- The coefficient lift comparison keeps the original coefficient and differential tensor values. -/
theorem tensorIso_hom_tmul (M : ModuleCat.{s} R) (X : ModuleCat.{v} R)
    (m : ULift.{h} M) (x : X) :
    (tensorIso.{u, v, s, h} R M X).hom.hom (m ⊗ₜ[R] x) = ULift.up (m.down ⊗ₜ[R] x) := by
  change (ULift.moduleEquiv : ULift.{h} (M ⊗[R] X) ≃ₗ[R] M ⊗[R] X).symm
    ((TensorProduct.congr (ULift.moduleEquiv : ULift.{h} M ≃ₗ[R] M)
      (LinearEquiv.refl R X)) (m ⊗ₜ[R] x)) = _
  rw [TensorProduct.congr_tmul]
  rfl

/-- The same native tensor comparison is natural in every original diagram map. -/
def tensorFunctorIso (M : ModuleCat.{s} R) :
    (tensorBifunctorAt.{u, max s h, v} R).obj ((uliftFunctor.{h, s} R).obj M) ≅
      (tensorBifunctorAt.{u, s, v} R).obj M ⋙ uliftFunctor.{h, max v s} R :=
  NatIso.ofComponents (tensorIso.{u, v, s, h} R M) (by
    intro X Y a
    apply ModuleCat.hom_ext
    apply TensorProduct.ext'
    intro m x
    simp only [ModuleCat.hom_comp]
    rfl)

/-- Native tensoring and native additive normalization identify the lifted coefficient
with the original model's native lift. -/
def normalizedIso (M : ModuleCat.{s} R) (X : SimplicialObject (ModuleCat.{v} R)) :
    ((SimplicialCoefficientFamilies.normalized.{u, v, max s h} R).obj X).obj
        ((uliftFunctor.{h, s} R).obj M) ≅
      ((uliftFunctor.{h, max v s} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((SimplicialCoefficientFamilies.normalized.{u, v, s} R).obj X).obj M) :=
  (normalizedMooreComplex (ModuleCat.{max v s h} R)).mapIso
      (Functor.isoWhiskerLeft X (tensorFunctorIso.{u, v, s, h} R M)) ≪≫
    (((NormalizedQuotient.mooreCompMapIso (uliftFunctor.{h, max v s} R)).app
      (X ⋙ (tensorBifunctorAt.{u, s, v} R).obj M))).symm

/-- The return to the original normalized model preserves every original fixed simplicial diagram map. -/
@[reassoc]
theorem normalizedIso_naturality (M : ModuleCat.{s} R)
    {X Y : SimplicialObject (ModuleCat.{v} R)} (f : X ⟶ Y) :
    ((SimplicialCoefficientFamilies.normalized.{u, v, max s h} R).map f).app
        ((uliftFunctor.{h, s} R).obj M) ≫ (normalizedIso.{u, v, s, h} R M Y).hom =
      (normalizedIso.{u, v, s, h} R M X).hom ≫
        ((uliftFunctor.{h, max v s} R).mapHomologicalComplex (ComplexShape.down ℕ)).map
          (((SimplicialCoefficientFamilies.normalized.{u, v, s} R).map f).app M) := by
  let T := (tensorBifunctorAt.{u, s, v} R).obj M
  let T' := (tensorBifunctorAt.{u, max s h, v} R).obj ((uliftFunctor.{h, s} R).obj M)
  let U := uliftFunctor.{h, max v s} R
  let N := normalizedMooreComplex (ModuleCat.{max v s} R)
  let N' := normalizedMooreComplex (ModuleCat.{max v s h} R)
  let sX := (Functor.isoWhiskerLeft X (tensorFunctorIso.{u, v, s, h} R M)).hom
  let sY := (Functor.isoWhiskerLeft Y (tensorFunctorIso.{u, v, s, h} R M)).hom
  let a := Functor.whiskerRight f T'
  let b := Functor.whiskerRight f (T ⋙ U)
  let c := Functor.whiskerRight f T
  let eX := ((NormalizedQuotient.mooreCompMapIso U).app (X ⋙ T))
  let eY := ((NormalizedQuotient.mooreCompMapIso U).app (Y ⋙ T))
  let d := (U.mapHomologicalComplex (ComplexShape.down ℕ)).map (N.map c)
  have hs : a ≫ sY = sX ≫ b := by
    apply NatTrans.ext
    funext i
    exact (tensorFunctorIso.{u, v, s, h} R M).hom.naturality (f.app i)
  have hsN : N'.map a ≫ N'.map sY = N'.map sX ≫ N'.map b :=
    (N'.map_comp a sY).symm.trans ((congrArg N'.map hs).trans (N'.map_comp sX b))
  have hu : d ≫ eY.hom = eX.hom ≫ N'.map b :=
    (NormalizedQuotient.mooreCompMapIso U).hom.naturality c
  have huInv : N'.map b ≫ eY.inv = eX.inv ≫ d := by
    apply (cancel_epi eX.hom).mp
    calc
      _ = (eX.hom ≫ N'.map b) ≫ eY.inv := (Category.assoc _ _ _).symm
      _ = (d ≫ eY.hom) ≫ eY.inv := congrArg (fun z => z ≫ eY.inv) hu.symm
      _ = d := by simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]
      _ = eX.hom ≫ (eX.inv ≫ d) := (Iso.hom_inv_id_assoc eX d).symm
  change N'.map a ≫ (N'.map sY ≫ eY.inv) = (N'.map sX ≫ eX.inv) ≫ d
  calc
    _ = (N'.map a ≫ N'.map sY) ≫ eY.inv := (Category.assoc _ _ _).symm
    _ = (N'.map sX ≫ N'.map b) ≫ eY.inv := congrArg (fun z => z ≫ eY.inv) hsN
    _ = N'.map sX ≫ (N'.map b ≫ eY.inv) := Category.assoc _ _ _
    _ = N'.map sX ≫ (eX.inv ≫ d) := congrArg (fun z => N'.map sX ≫ z) huInv
    _ = _ := (Category.assoc _ _ _).symm

/-- Represent independently sized original coefficient maps by the existing native module lifts. -/
def coefficientMap {M : ModuleCat.{s} R} {N : ModuleCat.{t} R} (a : M →ₗ[R] N) :
    (uliftFunctor.{max s t h, s} R).obj M ⟶ (uliftFunctor.{max s t h, t} R).obj N :=
  ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{max s t h} N ≃ₗ[R] N).symm.toLinearMap.comp
      (a.comp (ULift.moduleEquiv : ULift.{max s t h} M ≃ₗ[R] M).toLinearMap))

/-- The lifted coefficient map has exactly the original linear-map value. -/
theorem coefficientMap_up {M : ModuleCat.{s} R} {N : ModuleCat.{t} R} (a : M →ₗ[R] N) (m : M) :
    (coefficientMap.{u, s, t, h} R a).hom (ULift.up m) = ULift.up (a m) := rfl

/-- The tensor map in the common native world returns the original tensor of the original coefficient map. -/
theorem tensorCoefficientMap_tmul {M : ModuleCat.{s} R} {N : ModuleCat.{t} R}
    (a : M →ₗ[R] N) (X : ModuleCat.{v} R) (m : M) (x : X) :
    ((tensorIso.{u, v, t, max s t h} R N X).hom).hom
        ((tensorHomAt R (coefficientMap.{u, s, t, h} R a) (𝟙 X)).hom
          (ULift.up m ⊗ₜ[R] x)) = ULift.up (a m ⊗ₜ[R] x) := by
  let m' : (uliftFunctor.{max s t h, s} R).obj M := ULift.up m
  have hmap := tensorHomAt_tmul (R := R) (coefficientMap.{u, s, t, h} R a) (𝟙 X) m' x
  have hcoef : (coefficientMap.{u, s, t, h} R a).hom m' = ULift.up (a m) :=
    coefficientMap_up.{u, s, t, h} R a m
  rw [hcoef, ModuleCat.id_apply] at hmap
  change (tensorIso.{u, v, t, max s t h} R N X).hom.hom
      ((tensorHomAt R (coefficientMap.{u, s, t, h} R a) (𝟙 X)).hom (m' ⊗ₜ[R] x)) =
    ULift.up (a m ⊗ₜ[R] x)
  exact (congrArg (tensorIso.{u, v, t, max s t h} R N X).hom.hom hmap).trans
    (tensorIso_hom_tmul.{u, v, t, max s t h} R N X (ULift.up (a m)) x)

/-- Native coefficient lifting and the original tensor coefficient map commute
for independently sized original coefficients and the original diagram carrier. -/
@[reassoc]
theorem tensorIso_coefficientMap_naturality
    {M : ModuleCat.{s} R} {N : ModuleCat.{t} R} (a : M →ₗ[R] N) (X : ModuleCat.{v} R) :
    tensorHomAt R (coefficientMap.{u, s, t, max v s t h} R a) (𝟙 X) ≫
        (tensorIso.{u, v, t, max v s t h} R N X).hom =
      (tensorIso.{u, v, s, max v s t h} R M X).hom ≫
        coefficientMap.{u, max v s, max v t, max v s t h} R
          (TensorProduct.map a (LinearMap.id : X →ₗ[R] X)) := by
  apply ModuleCat.hom_ext
  apply TensorProduct.ext'
  rintro ⟨m⟩ x
  change (tensorIso.{u, v, t, max v s t h} R N X).hom.hom
      ((tensorHomAt R (coefficientMap.{u, s, t, max v s t h} R a) (𝟙 X)).hom
        (ULift.up m ⊗ₜ[R] x)) =
    (coefficientMap.{u, max v s, max v t, max v s t h} R
      (TensorProduct.map a (LinearMap.id : X →ₗ[R] X))).hom
        ((tensorIso.{u, v, s, max v s t h} R M X).hom.hom (ULift.up m ⊗ₜ[R] x))
  rw [tensorCoefficientMap_tmul, tensorIso_hom_tmul, coefficientMap_up,
    TensorProduct.map_tmul, LinearMap.id_apply]

end ModuleCat.SimplicialCoefficientLift

end
