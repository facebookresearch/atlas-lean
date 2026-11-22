/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceOperatorFunctor

/-!
# Actual native morphisms from original source sphere morphisms

A genuine source enriched transformation preserving the entire original
sphere structure maps gives a genuine transformation between the original
reverse functors. Every original component is retained. Original canonical
morphisms use their actual full sphere and operator naturality.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory MonoidalCategory
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceOperatorMorphism

/-- The original orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original block-sum monoidal structure on orthogonal indices. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed CGWH enriched ordinary structure on orthogonal indices. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block symmetry on orthogonal indices. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}

attribute [local instance] Enriched.prodCategory

variable
  (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  (t : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (X.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} X.toEnrichedFunctor))
  (hu : ∀ n : OrthogonalIndex,
    (X.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.epsilon) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n 0 ≫
      X.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
        (ρ_ (X.toEnrichedFunctor.obj n)).hom)
  (ha : ∀ n a b : OrthogonalIndex,
    (α_ (X.toEnrichedFunctor.obj n) (PointedCGWH.orthogonalSphere.{u, v} a)
      (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      (Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ▷
          PointedCGWH.orthogonalSphere.{u, v} b) ≫
        Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t (n + a) b =
    (X.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.mu a b) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n (a + b) ≫
          X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv)

variable
  (Y : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
  (s : GradedNatTrans ((Center.ofBraided PointedCGWH.{u, v}).obj (𝟙_ PointedCGWH.{u, v}))
    (Y.toEnrichedFunctor.externalTensor orthogonalSphereFunctor.{u, v})
    (OrthogonalIndex.enrichedMonoidalData.{u, v}.tensorEnrichedFunctor.comp
      PointedCGWH.{u, v} Y.toEnrichedFunctor))
  (hv : ∀ n : OrthogonalIndex,
    (Y.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.epsilon) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n 0 ≫
      Y.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
        (ρ_ (Y.toEnrichedFunctor.obj n)).hom)
  (hb : ∀ n a b : OrthogonalIndex,
    (α_ (Y.toEnrichedFunctor.obj n) (PointedCGWH.orthogonalSphere.{u, v} a)
      (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      (Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n a ▷
          PointedCGWH.orthogonalSphere.{u, v} b) ≫
        Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
          orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s (n + a) b =
    (Y.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.mu a b) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n (a + b) ≫
          Y.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv)

variable (q : X ⟶ Y)
  (hq : ∀ n a : OrthogonalIndex,
    Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X.toEnrichedFunctor t n a ≫
        EnrichedFunctorCat.component q (n + a) =
    (EnrichedFunctorCat.component q n ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
      Reconstruction.sphereComponent OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} Y.toEnrichedFunctor s n a)

/-- The original source sphere morphism gives a genuine whole native transformation. -/
def reverseMap : CanonicalSourceOperatorFunctor.reverseFunctor X t hu ha ⟶
    CanonicalSourceOperatorFunctor.reverseFunctor Y s hv hb :=
  GradedNatTrans.unitOfComponents
    (fun n => EnrichedFunctorCat.component q n.asIndex)
    (by
      intro n k
      exact CanonicalSourceActionCompatibility.reverseOperatorMapField_morphism
        t s q hq n.asIndex k.asIndex)

/-- Every entire original source component is the corresponding native component. -/
theorem reverseMap_component (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (reverseMap X t hu ha Y s hv hb q hq)
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) = EnrichedFunctorCat.component q n :=
  GradedNatTrans.unitOfComponents_component _ _ (OrthogonalOperatorIndex.ofIndex.{u, v} n)

/-- The whole native app function is the literal original source component supplier. -/
theorem reverseMap_fullApp :
    (reverseMap X t hu ha Y s hv hb q hq).app =
      fun (n : OrthogonalOperatorIndex.{u, v}) =>
        eHomEquiv PointedCGWH.{u, v} (EnrichedFunctorCat.component q n.asIndex) := by
  funext n
  exact GradedNatTrans.unitOfComponents_app _ _ n

/-- Actual original canonical morphisms have their full native reconstruction. -/
def originalReverseMap
    {F G : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})} (f : F ⟶ G) :
    CanonicalSourceOperatorFunctor.originalReverseFunctor F ⟶
      CanonicalSourceOperatorFunctor.originalReverseFunctor G :=
  GradedNatTrans.unitOfComponents
    (fun n => EnrichedFunctorCat.component f n)
    (by
      intro n k
      exact CanonicalSourceActionCompatibility.original_reverseOperatorMapField_morphism
        f n.asIndex k.asIndex)

/-- Every original canonical component is retained by actual native reconstruction. -/
theorem originalReverseMap_component
    {F G : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})} (f : F ⟶ G)
    (n : OrthogonalOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (originalReverseMap f) n = EnrichedFunctorCat.component f n :=
  GradedNatTrans.unitOfComponents_component _ _ n

/-- Both complete native component functions agree for every original canonical morphism. -/
theorem originalReverseMap_fullApp
    {F G : (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v})} (f : F ⟶ G) :
    (originalReverseMap f).app = f.app := by
  funext n
  calc
    (originalReverseMap f).app n =
        eHomEquiv PointedCGWH.{u, v} (EnrichedFunctorCat.component f n) :=
      GradedNatTrans.unitOfComponents_app _ _ n
    _ = f.app n := (eHomEquiv PointedCGWH.{u, v}).apply_symm_apply (f.app n)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceOperatorMorphism
