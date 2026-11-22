/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.Spectra.Symmetric.OrthogonalIndex
import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereFunctor
import MathlibExt.CategoryTheory.Enriched.Restriction

/-!
# Concrete restriction along the native finite-bijection index map

Restriction retains the original finite dimensions, every whole enriched Hom
action and all original transformation components. The representation-sphere
action on a finite bijection is exactly its compactified coordinate isometry.
This establishes the bare index action interface, without replacing the
original symmetric sphere coefficient.
-/

set_option autoImplicit false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra

attribute [local instance] OrthogonalIndex.enrichedCategory

private abbrev restrictedOrthogonalDiagram
    (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  EnrichedFunctorCat.toEnrichedFunctor
    ((EnrichedFunctorCat.restriction symmetricOrthogonalIndexFunctor.{u, v}).obj X)

/-- The original orthogonal sphere action of a finite bijection is its compactified isometry. -/
theorem finiteBijectionMatrix_sphereMap {m n : ℕ} (e : Fin m ≃ Fin n) :
    orthogonalSphereMap.{u, v} (OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix e)) =
      (orthogonalSphereCoordinateIso.{u, v} e).hom := by
  rw [orthogonalSphereMap_matrixPoint, finiteBijectionMatrix_isometry]
  rfl

/-- The literal finite-vector action has the original forward-coordinate convention. -/
theorem finiteBijectionMatrix_sphereMap_coe {m n : ℕ} (e : Fin m ≃ Fin n)
    (x : EuclideanSpace ℝ (Fin m)) :
    (orthogonalSphereMap.{u, v}
      (OrthogonalIndex.matrixPoint.{u, v} (finiteBijectionMatrix e))).right
      ((ULift.up x : ULift.{v, 0} (EuclideanSpace ℝ (Fin m))) :
        OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin m)))) =
      ((ULift.up ((EuclideanSpace.equiv (Fin n) ℝ).symm (x.ofLp ∘ e.symm)) :
        ULift.{v, 0} (EuclideanSpace ℝ (Fin n))) :
          OnePoint (ULift.{v, 0} (EuclideanSpace ℝ (Fin n)))) := by
  rw [orthogonalSphereMap_matrixPoint_coe, finiteBijectionMatrix_mulVec]

/-- Every original symmetric-index arrow has its actual one-point coordinate action. -/
theorem smallBijectionMatrix_sphereMap {A B : Operad.SmallFinBijGroupoid} (f : A ⟶ B) :
    orthogonalSphereMap.{u, v} (OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix f)) =
      (orthogonalSphereCoordinateIso.{u, v} (smallFiniteBijection f)).hom :=
  finiteBijectionMatrix_sphereMap.{u, v} (smallFiniteBijection f)

/-- Restriction keeps the full original finite cardinality object. -/
theorem symmetricOrthogonalRestriction_obj
    (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
    (A : Operad.SmallFinBijGroupoid) :
    (restrictedOrthogonalDiagram X).obj
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A) =
      X.toEnrichedFunctor.obj A.of.len := rfl

/-- Restriction precomposes the entire original orthogonal Hom action with the full copower map. -/
theorem symmetricOrthogonalRestriction_fullMap
    (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
    (A B : Operad.SmallFinBijGroupoid) :
    (restrictedOrthogonalDiagram X).map
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A)
        (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid B) =
      symmetricOrthogonalHomMap.{u, v} A B ≫ X.toEnrichedFunctor.map A.of.len B.of.len := rfl

/-- Every permutation uses the original orthogonal action of its matrix point. -/
theorem symmetricOrthogonalRestriction_generator
    (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
    {A B : Operad.SmallFinBijGroupoid} (f : A ⟶ B) :
    PointedCGWH.basedDiscreteIncl.{u, v, 0} (A ⟶ B) f ≫
      (restrictedOrthogonalDiagram X).map
          (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A)
          (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid B) =
      OrthogonalIndex.matrixPoint.{u, v} (smallBijectionMatrix f) ≫
        X.toEnrichedFunctor.map A.of.len B.of.len := by
  change PointedCGWH.basedDiscreteIncl.{u, v, 0} (A ⟶ B) f ≫
    (symmetricOrthogonalHomMap.{u, v} A B ≫ X.toEnrichedFunctor.map A.of.len B.of.len) = _
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (fun q => q ≫ X.toEnrichedFunctor.map A.of.len B.of.len)
      (symmetricOrthogonalHomMap_generator.{u, v} f))

/-- Concrete forgetting preserves every actual orthogonal transformation component. -/
theorem symmetricOrthogonalRestriction_component
    {X Y : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex} (t : X ⟶ Y)
    (A : Operad.SmallFinBijGroupoid) :
    EnrichedFunctorCat.component
      ((EnrichedFunctorCat.restriction symmetricOrthogonalIndexFunctor.{u, v}).map t)
      (PointedCGWH.copowerIndexObj.{u, v, 0} Operad.SmallFinBijGroupoid A) =
        EnrichedFunctorCat.component t A.of.len :=
  EnrichedFunctorCat.restrictionMap_component symmetricOrthogonalIndexFunctor.{u, v} t A

end CategoryTheory.Spectra
