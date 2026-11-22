/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.NativeOperatorIndex
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorRightAction
public import MathlibExt.CategoryTheory.Enriched.SphereOperatorIndexUnitComparison

/-!
# Original continuous orthogonal isometry and right sphere actions

The index inclusion is the already constructed full unit-coefficient functor,
whose entire map function agrees with the original native delta. The sphere
inclusion agrees with the original native nu. Restriction and its morphism
components use the existing genuine enriched-functor operations. The full
right Day generator family is specialized to the original representation
sphere and continuous orthogonal Hom values. No module or model dictionary
is supplied or declared by these action constructions.
-/

@[expose] public section

set_option autoImplicit false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open scoped MonoidalClosed

namespace CategoryTheory.Spectra.OrthogonalSourceRightModule

open Enriched.SphereOperator

attribute [local instance] OrthogonalIndex.category OrthogonalIndex.monoidalCategory
attribute [local instance] OrthogonalIndex.enrichedOrdinaryCategory
attribute [local instance] OrthogonalIndex.symmetricCategory

/-- The entire original native delta is the same full unit-coefficient Hom inclusion. -/
theorem indexHom_eq_original_delta (n k : OrthogonalIndex) :
    indexHom OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k =
        OrthogonalOperatorIndex.delta.{u, v} n k := by
  exact indexHom_eq_unit_padded OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k

/-- Every entire native Hom inclusion agrees as one original map function. -/
theorem indexHom_eq_original_delta_function :
    (fun n k : OrthogonalIndex =>
      indexHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} n k) =
      OrthogonalOperatorIndex.delta.{u, v} := by
  funext n k
  exact indexHom_eq_original_delta.{u, v} n k

/-- The original native right sphere inclusion uses the actual ordered block swap. -/
theorem rightSphereHom_eq_original_nu (n a : OrthogonalIndex) :
    rightSphereHom OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} n a = OrthogonalOperatorIndex.nu.{u, v} n a := by
  dsimp only [rightSphereHom, coefficientHom, OrthogonalOperatorIndex.nu,
    OrthogonalOperatorIndex.ι]
  exact Category.assoc _ _ _

/-- The complete native sphere-inclusion function is the original source nu. -/
theorem rightSphereHom_eq_original_nu_function :
    (fun n a : OrthogonalIndex =>
      rightSphereHom OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} n a) = OrthogonalOperatorIndex.nu.{u, v} := by
  funext n a
  exact rightSphereHom_eq_original_nu.{u, v} n a

/-- The actual native index inclusion retains its original enriched identity and composition. -/
def indexFunctor :
    EnrichedFunctor PointedCGWH.{u, v} OrthogonalIndex OrthogonalOperatorIndex.{u, v} :=
  indexUnitFunctor OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}

/-- Its objects are the original tagged native objects. -/
theorem indexFunctor_obj (n : OrthogonalIndex) :
    indexFunctor.{u, v}.obj n = OrthogonalOperatorIndex.ofIndex.{u, v} n := rfl

/-- Its entire map is the original continuous native delta. -/
theorem indexFunctor_map (n k : OrthogonalIndex) :
    indexFunctor.{u, v}.map n k = OrthogonalOperatorIndex.delta.{u, v} n k :=
  indexHom_eq_original_delta.{u, v} n k

/-- Restrict the whole original operator diagram by the actual full index inclusion. -/
def restrictionFunctor :
    EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v} ⥤
      EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex :=
  EnrichedFunctorCat.restriction indexFunctor.{u, v}

/-- Restriction is the same whole original unit-coefficient supplier call. -/
theorem restrictionFunctor_eq :
    restrictionFunctor.{u, v} =
      indexRestriction OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} := rfl

/-- The restricted continuous I-space keeps each entire original value. -/
theorem restrictionFunctor_obj
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n : OrthogonalIndex) :
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.obj n =
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) := rfl

/-- Every complete native isometry Hom acts through the original delta and full operator action. -/
theorem restrictionFunctor_full_map
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n k : OrthogonalIndex) :
    ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.map n k =
      OrthogonalOperatorIndex.delta.{u, v} n k ≫
        F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
          (OrthogonalOperatorIndex.ofIndex.{u, v} k) := by
  let f := F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
    (OrthogonalOperatorIndex.ofIndex.{u, v} k)
  have h :
      ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor.map n k =
        indexFunctor.{u, v}.map n k ≫ f :=
    EnrichedFunctorCat.restriction_fullMap indexFunctor.{u, v} F n k
  exact h.trans (congrArg (fun z => z ≫ f) (indexFunctor_map.{u, v} n k))

/-- Every original morphism retains its whole original component after restriction. -/
theorem restrictionFunctor_map_component
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}}
    (q : F ⟶ G) (n : OrthogonalIndex) :
    EnrichedFunctorCat.component ((restrictionFunctor.{u, v}).map q) n =
      EnrichedFunctorCat.component q (OrthogonalOperatorIndex.ofIndex.{u, v} n) :=
  EnrichedFunctorCat.restrictionMap_component indexFunctor.{u, v} q n

/-- The original native right sphere structure map of every whole operator diagram. -/
def sphereAction
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n a : OrthogonalIndex) :
    F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ⊗
      PointedCGWH.orthogonalSphere.{u, v} a ⟶
      F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) :=
  rightSphereAction OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} F n a

/-- The whole structure map acts by the actual original source nu, with no new choice. -/
theorem sphereAction_original_nu
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (n a : OrthogonalIndex) :
    sphereAction.{u, v} F n a =
      (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) ◁
        OrthogonalOperatorIndex.nu.{u, v} n a) ≫
        MonoidalClosed.uncurry
          (F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
            (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a))) := by
  dsimp only [sphereAction, rightSphereAction, coefficientAction]
  rw [← rightSphereHom_eq_original_nu]
  rfl

/-- All original genuine morphisms retain the full right structure maps. -/
theorem sphereAction_natural
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}}
    (q : F ⟶ G) (n a : OrthogonalIndex) :
    sphereAction.{u, v} F n a ≫
      EnrichedFunctorCat.component q (OrthogonalOperatorIndex.ofIndex.{u, v} (n + a)) =
    (EnrichedFunctorCat.component q (OrthogonalOperatorIndex.ofIndex.{u, v} n) ▷
      PointedCGWH.orthogonalSphere.{u, v} a) ≫ sphereAction.{u, v} G n a :=
  rightSphereAction_natural OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} q n a

attribute [local instance] Enriched.prodCategory

/-- The actual original continuous two-factor Day generator family at every level. -/
def dayGenerator
    (F : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})
    (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) :
    EnrichedDayKernel.objects OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor
      ((restrictionFunctor.{u, v}).obj F).toEnrichedFunctor
      orthogonalSphereFunctor.{u, v} k a ⟶
        F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} k) :=
  rightDayActionGenerator OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} F k a

/-- Every actual spectrum morphism respects the entire native Day generator family. -/
theorem dayGenerator_natural
    {F G : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}}
    (q : F ⟶ G) (k : OrthogonalIndex) (a : OrthogonalIndex × OrthogonalIndex) :
    dayGenerator.{u, v} F k a ≫
      EnrichedFunctorCat.component q (OrthogonalOperatorIndex.ofIndex.{u, v} k) =
    (𝟙 (OrthogonalIndex.hom.{u, v} (a.1 + a.2) k) ⊗ₘ
      (EnrichedFunctorCat.component q (OrthogonalOperatorIndex.ofIndex.{u, v} a.1) ⊗ₘ
        𝟙 (PointedCGWH.orthogonalSphere.{u, v} a.2))) ≫ dayGenerator.{u, v} G k a :=
  rightDayActionGenerator_natural OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} q k a

end CategoryTheory.Spectra.OrthogonalSourceRightModule
