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
# Lifting coefficients and normalized tensor complexes

For a commutative ring R and modules M and X at independent carrier heights, the tensor (ULift
M) ⊗_R X is canonically isomorphic to ULift(M ⊗_R X). The forward map sends m ⊗ x to the lift
of m.down ⊗ x.

For a simplicial diagram X, these isomorphisms are natural and give N((ULift M) ⊗_R X) ≅ ULift
N(M ⊗_R X). A linear coefficient map between independently sized modules is represented at a
common lift height by up(m) ↦ up(a(m)); the tensor and normalization comparisons retain this
coefficient map.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v s t h

namespace ModuleCat.SimplicialCoefficientLift

variable (R : Type u) [CommRing R]

/-- The tensor isomorphism for a lifted coefficient.

The canonical R-linear isomorphism identifies (ULift M) ⊗_R X with ULift(M ⊗_R X), with
separate coefficient, diagram and lift heights. -/
def tensorIso (M : ModuleCat.{s} R) (X : ModuleCat.{v} R) :
    tensorObjAt R ((uliftFunctor.{h, s} R).obj M) X ≅
      (uliftFunctor.{h, max v s} R).obj (tensorObjAt R M X) :=
  ((TensorProduct.congr (ULift.moduleEquiv : ULift.{h} M ≃ₗ[R] M)
      (LinearEquiv.refl R X)).trans
    (ULift.moduleEquiv : ULift.{h} (M ⊗[R] X) ≃ₗ[R] M ⊗[R] X).symm).toModuleIso

/-- The lifted coefficient tensor map on pure tensors.

For m ∈ ULift M and x ∈ X, the forward comparison sends m ⊗ x to ULift.up(m.down ⊗ x). -/
theorem tensorIso_hom_tmul (M : ModuleCat.{s} R) (X : ModuleCat.{v} R)
    (m : ULift.{h} M) (x : X) :
    (tensorIso.{u, v, s, h} R M X).hom.hom (m ⊗ₜ[R] x) = ULift.up (m.down ⊗ₜ[R] x) := by
  change (ULift.moduleEquiv : ULift.{h} (M ⊗[R] X) ≃ₗ[R] M ⊗[R] X).symm
    ((TensorProduct.congr (ULift.moduleEquiv : ULift.{h} M ≃ₗ[R] M)
      (LinearEquiv.refl R X)) (m ⊗ₜ[R] x)) = _
  rw [TensorProduct.congr_tmul]
  rfl

/-- Naturality of the lifted coefficient tensor isomorphism.

For fixed M, the tensor comparisons give a natural isomorphism between (ULift M) ⊗_R − and M
⊗_R − followed by module lifting. -/
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

/-- The normalized Moore comparison for lifted coefficients.

For a simplicial X, normalization of (ULift M) ⊗_R X is isomorphic to the module lift of N(M
⊗_R X), using the tensor comparison and the normalization–lift isomorphism. -/
def normalizedIso (M : ModuleCat.{s} R) (X : SimplicialObject (ModuleCat.{v} R)) :
    ((SimplicialCoefficientFamilies.normalized.{u, v, max s h} R).obj X).obj
        ((uliftFunctor.{h, s} R).obj M) ≅
      ((uliftFunctor.{h, max v s} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((SimplicialCoefficientFamilies.normalized.{u, v, s} R).obj X).obj M) :=
  (normalizedMooreComplex (ModuleCat.{max v s h} R)).mapIso
      (Functor.isoWhiskerLeft X (tensorFunctorIso.{u, v, s, h} R M)) ≪≫
    (((NormalizedQuotient.mooreCompMapIso (uliftFunctor.{h, max v s} R)).app
      (X ⋙ (tensorBifunctorAt.{u, s, v} R).obj M))).symm

/-- Diagram naturality of the normalized coefficient-lift comparison.

For f : X → Y, the normalized map with lifted coefficient M followed by the comparison for Y
equals the comparison for X followed by the lift of the normalized map with coefficient M. -/
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

/-- A coefficient linear map represented at a common lift height.

For a : M →ₗ[R] N with independent source and target carrier heights, lift both modules to the
stated common height and send up(m) to up(a(m)). -/
def coefficientMap {M : ModuleCat.{s} R} {N : ModuleCat.{t} R} (a : M →ₗ[R] N) :
    (uliftFunctor.{max s t h, s} R).obj M ⟶ (uliftFunctor.{max s t h, t} R).obj N :=
  ModuleCat.ofHom
    ((ULift.moduleEquiv : ULift.{max s t h} N ≃ₗ[R] N).symm.toLinearMap.comp
      (a.comp (ULift.moduleEquiv : ULift.{max s t h} M ≃ₗ[R] M).toLinearMap))

/-- Coordinates of the lifted coefficient morphism.

The common-height coefficient map sends ULift.up m to ULift.up(a m). -/
theorem coefficientMap_up {M : ModuleCat.{s} R} {N : ModuleCat.{t} R} (a : M →ₗ[R] N) (m : M) :
    (coefficientMap.{u, s, t, h} R a).hom (ULift.up m) = ULift.up (a m) := rfl

/-- The lifted tensor coefficient map on generators.

Apply the lifted coefficient map to up(m) ⊗ x and then the target tensor comparison. The
result is up(a(m) ⊗ x). -/
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

/-- The tensor comparison square for a heterogeneous coefficient map.

Tensoring the common-height lift of a with id_X then applying the target comparison equals
applying the source comparison then lifting TensorProduct.map a id_X. -/
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
