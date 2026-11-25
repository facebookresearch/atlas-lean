/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- SOURCE-ONLY needed original-output transport; Native has not been run.
module

public import MathlibExt.Algebra.Category.ModuleCat.SimplicialCoefficientLift

/-!
# Actual coefficient maps on lifted original normalized tensor models

Independently sized coefficients are compared through the native coefficient
lifts and the already earned tensor isomorphisms. The map on lifted original
tensor diagrams has exactly the native lift of TensorProduct.map a id in each
degree. Native additive normalization then gives a map between the lifts of
the original normalized models. Its comparison square uses the existing
normalizedIso, without an assumed naturality or output-transport certificate.
-/

@[expose] public section
noncomputable section

open CategoryTheory AlgebraicTopology
open scoped Simplicial TensorProduct

universe u v s t h

namespace ModuleCat.SimplicialCoefficientLiftNaturality

open ModuleCat.SimplicialCoefficientLift

variable (R : Type u) [CommRing R]
  {M : ModuleCat.{s} R} {N : ModuleCat.{t} R}

/-- The actual coefficient map on the fixed simplicial diagram in one native
coefficient world, retaining the original heterogeneous linear map. -/
def liftedTensorMap (a : M →ₗ[R] N) (X : SimplicialObject (ModuleCat.{v} R)) :
    X ⋙ (tensorBifunctorAt.{u, max v s t h, v} R).obj
        ((uliftFunctor.{max v s t h, s} R).obj M) ⟶
      X ⋙ (tensorBifunctorAt.{u, max v s t h, v} R).obj
        ((uliftFunctor.{max v s t h, t} R).obj N) :=
  Functor.whiskerLeft X ((tensorBifunctorAt.{u, max v s t h, v} R).map
    (coefficientMap.{u, s, t, max v s t h} R a))

/-- Return that same coefficient map to the native lifts of the original
unmodified tensor diagrams through the actual tensor comparison. -/
def outputTensorMap (a : M →ₗ[R] N) (X : SimplicialObject (ModuleCat.{v} R)) :
    (X ⋙ (tensorBifunctorAt.{u, s, v} R).obj M) ⋙ uliftFunctor.{max v s t h, max v s} R ⟶
      (X ⋙ (tensorBifunctorAt.{u, t, v} R).obj N) ⋙ uliftFunctor.{max v s t h, max v t} R :=
  (Functor.isoWhiskerLeft X (tensorFunctorIso.{u, v, s, max v s t h} R M)).inv ≫
    liftedTensorMap.{u, v, s, t, h} R a X ≫
      (Functor.isoWhiskerLeft X (tensorFunctorIso.{u, v, t, max v s t h} R N)).hom

/-- The map is exactly the native lift of the original tensor coefficient map,
with the same original diagram and original coefficient-map values. -/
theorem outputTensorMap_app (a : M →ₗ[R] N)
    (X : SimplicialObject (ModuleCat.{v} R)) (i : SimplexCategoryᵒᵖ) :
    (outputTensorMap.{u, v, s, t, h} R a X).app i =
      coefficientMap.{u, max v s, max v t, max v s t h} R
        (M := tensorObjAt R M (X.obj i)) (N := tensorObjAt R N (X.obj i))
        (TensorProduct.map a (LinearMap.id : X.obj i →ₗ[R] X.obj i)) := by
  let eM := tensorIso.{u, v, s, max v s t h} R M (X.obj i)
  let eN := tensorIso.{u, v, t, max v s t h} R N (X.obj i)
  let c := coefficientMap.{u, max v s, max v t, max v s t h} R
    (M := tensorObjAt R M (X.obj i)) (N := tensorObjAt R N (X.obj i))
    (TensorProduct.map a (LinearMap.id : X.obj i →ₗ[R] X.obj i))
  have hc := tensorIso_coefficientMap_naturality.{u, v, s, t, h} R a (X.obj i)
  change eM.inv ≫
      (tensorHomAt R (coefficientMap.{u, s, t, max v s t h} R a) (𝟙 (X.obj i)) ≫ eN.hom) = c
  exact (congrArg (fun z => eM.inv ≫ z) hc).trans (Iso.inv_hom_id_assoc eM c)

/-- Native additive normalization of the actual lifted original tensor map,
returned to the lifts of the original normalized coefficient models. -/
def outputNormalizedMap (a : M →ₗ[R] N)
    (X : SimplicialObject (ModuleCat.{v} R)) :
    ((uliftFunctor.{max v s t h, max v s} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((SimplicialCoefficientFamilies.normalized.{u, v, s} R).obj X).obj M) ⟶
      ((uliftFunctor.{max v s t h, max v t} R).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (((SimplicialCoefficientFamilies.normalized.{u, v, t} R).obj X).obj N) :=
  (((NormalizedQuotient.mooreCompMapIso (uliftFunctor.{max v s t h, max v s} R)).app
    (X ⋙ (tensorBifunctorAt.{u, s, v} R).obj M))).hom ≫
    (normalizedMooreComplex (ModuleCat.{max v s t h} R)).map
      (outputTensorMap.{u, v, s, t, h} R a X) ≫
      (((NormalizedQuotient.mooreCompMapIso (uliftFunctor.{max v s t h, max v t} R)).app
        (X ⋙ (tensorBifunctorAt.{u, t, v} R).obj N))).inv

/-- The same existing normalized tensor-lift isomorphisms respect the actual
original-output coefficient map for independently sized original modules. -/
@[reassoc]
theorem normalizedIso_coefficientMap_naturality (a : M →ₗ[R] N)
    (X : SimplicialObject (ModuleCat.{v} R)) :
    ((SimplicialCoefficientFamilies.normalized.{u, v, max v s t h} R).obj X).map
        (coefficientMap.{u, s, t, max v s t h} R a) ≫
      (normalizedIso.{u, v, t, max v s t h} R N X).hom =
    (normalizedIso.{u, v, s, max v s t h} R M X).hom ≫
      outputNormalizedMap.{u, v, s, t, h} R a X := by
  let eM := Functor.isoWhiskerLeft X (tensorFunctorIso.{u, v, s, max v s t h} R M)
  let eN := Functor.isoWhiskerLeft X (tensorFunctorIso.{u, v, t, max v s t h} R N)
  let A := liftedTensorMap.{u, v, s, t, h} R a X
  let B := outputTensorMap.{u, v, s, t, h} R a X
  let N' := normalizedMooreComplex (ModuleCat.{max v s t h} R)
  let EM := ((NormalizedQuotient.mooreCompMapIso (uliftFunctor.{max v s t h, max v s} R)).app
    (X ⋙ (tensorBifunctorAt.{u, s, v} R).obj M))
  let EN := ((NormalizedQuotient.mooreCompMapIso (uliftFunctor.{max v s t h, max v t} R)).app
    (X ⋙ (tensorBifunctorAt.{u, t, v} R).obj N))
  have hs : eM.hom ≫ B = A ≫ eN.hom := by
    change eM.hom ≫ (eM.inv ≫ A ≫ eN.hom) = A ≫ eN.hom
    simp only [Iso.hom_inv_id_assoc]
  have hN : N'.map eM.hom ≫ N'.map B = N'.map A ≫ N'.map eN.hom :=
    (N'.map_comp eM.hom B).symm.trans ((congrArg N'.map hs).trans (N'.map_comp A eN.hom))
  change N'.map A ≫ (N'.map eN.hom ≫ EN.inv) =
    (N'.map eM.hom ≫ EM.inv) ≫ (EM.hom ≫ N'.map B ≫ EN.inv)
  calc
    _ = (N'.map A ≫ N'.map eN.hom) ≫ EN.inv := (Category.assoc _ _ _).symm
    _ = (N'.map eM.hom ≫ N'.map B) ≫ EN.inv := congrArg (fun z => z ≫ EN.inv) hN.symm
    _ = _ := by simp only [Category.assoc, Iso.inv_hom_id_assoc]

end ModuleCat.SimplicialCoefficientLiftNaturality

end
