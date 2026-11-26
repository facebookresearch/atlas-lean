/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Coefficient maps between lifted normalized tensor complexes.
module

public import MathlibExt.Algebra.Category.ModuleCat.SimplicialCoefficientLift

/-!
# Coefficient maps between lifted normalized tensor models

For a linear map a : M → N between independently sized R-modules and a simplicial module
diagram X, lift both coefficients to a common carrier height. Tensoring a with X gives a map
of the lifted-coefficient diagrams. The tensor comparison identifies it with the lift of a ⊗
id_X on M ⊗_R X.

After passing to normalized Moore complexes and using the normalization–lift comparisons, this
gives a map between the lifts of the normalized complexes with coefficients M and N. The
normalized coefficient-lift isomorphisms commute with this map.
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

/-- The simplicial tensor map between common-height coefficient lifts.

For a : M →ₗ[R] N, tensor its common-height lift on the left with each object of X to obtain
(ULift M) ⊗_R X → (ULift N) ⊗_R X. -/
def liftedTensorMap (a : M →ₗ[R] N) (X : SimplicialObject (ModuleCat.{v} R)) :
    X ⋙ (tensorBifunctorAt.{u, max v s t h, v} R).obj
        ((uliftFunctor.{max v s t h, s} R).obj M) ⟶
      X ⋙ (tensorBifunctorAt.{u, max v s t h, v} R).obj
        ((uliftFunctor.{max v s t h, t} R).obj N) :=
  Functor.whiskerLeft X ((tensorBifunctorAt.{u, max v s t h, v} R).map
    (coefficientMap.{u, s, t, max v s t h} R a))

/-- The coefficient map on lifts of the tensor diagrams.

Conjugate the lifted-coefficient simplicial map by the tensor comparison isomorphisms to
obtain ULift(M ⊗_R X) → ULift(N ⊗_R X). -/
def outputTensorMap (a : M →ₗ[R] N) (X : SimplicialObject (ModuleCat.{v} R)) :
    (X ⋙ (tensorBifunctorAt.{u, s, v} R).obj M) ⋙ uliftFunctor.{max v s t h, max v s} R ⟶
      (X ⋙ (tensorBifunctorAt.{u, t, v} R).obj N) ⋙ uliftFunctor.{max v s t h, max v t} R :=
  (Functor.isoWhiskerLeft X (tensorFunctorIso.{u, v, s, max v s t h} R M)).inv ≫
    liftedTensorMap.{u, v, s, t, h} R a X ≫
      (Functor.isoWhiskerLeft X (tensorFunctorIso.{u, v, t, max v s t h} R N)).hom

/-- The component formula for the lifted tensor-diagram map.

At i, outputTensorMap is the common-height lift of TensorProduct.map a id_{X_i}, acting on the
first tensor coefficient. -/
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

/-- The map between lifted normalized tensor complexes.

Normalize outputTensorMap and use the normalization–lift isomorphisms to obtain a chain map
between the lifts of the normalized Moore complexes of M ⊗_R X and N ⊗_R X. -/
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

/-- The normalized lift comparison square for coefficient maps.

The normalized map of the common-height coefficient lift followed by the target normalized
comparison equals the source comparison followed by outputNormalizedMap. -/
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
