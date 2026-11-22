/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Native.SequentialSymmetricInductionComparison.Core
import MathlibExt.CategoryTheory.Adjunction.TripleComposition
import MathlibExt.CategoryTheory.Monoidal.Mod.ExtensionOfScalarsAdjunction

/-!
# The complete original balanced induction adjunction

Both Hom functions, inverse laws, source and target naturality, unit, counit
and triangle maps retain the original monoidal lift and balanced scalar
induction on every native sequential and symmetric spectrum.
-/

set_option autoImplicit false
noncomputable section
open CategoryTheory CategoryTheory.Functor CategoryTheory.Spectra Limits MonoidalCategory
open scoped MonoidalClosed ExternalProduct CategoryTheory.MonObj CategoryTheory.Obj


namespace PointedCGWH.Spectra.SequentialSymmetricInductionComparison
universe u v
attribute [local instance] PointedCGWH.EnrichedKan.hasSmallColimits
  originalSymmetricSequenceMonoidal originalSymmetricSequenceBraided originalSymmetricSequenceSymmetric
  degreeInclusionMonoidal restrictionLaxMonoidal symmetrizationOplaxMonoidal sequenceAdjunctionIsMonoidal
  symmetrizationMonoidal orderedSphereMonObj sphereSequenceMonObj tensorSphereMap_isMonHom
  symmetricSequenceClosed symmetricSequenceColimits symmetricTensorLeftPreservesColimits

/-- The original balanced module Hom function is the full original scalar Hom function followed by the monoidal lift. -/
theorem moduleAdjunction_homEquiv_original
    (M : Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v})
    (N : Mod SymmetricSequence.{u, v} sphereSequence.{u, v})
    (f : moduleInduction.{u, v}.obj M ⟶ N) :
    moduleAdjunction.{u, v}.homEquiv M N f =
      (Mod.MonoidalAdjunction.adjunction sequenceAdjunction.{u, v} orderedSphere.{u, v}).homEquiv M
        ((Mod.ExtensionOfScalars.restriction tensorSphereMap.{u, v}).obj N)
        (Mod.ExtensionOfScalars.homEquiv tensorSphereMap.{u, v}
          ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M) N f) :=
  CategoryTheory.Mod.MonoidalAdjunction.extensionOfScalarsAdjunction_homEquiv
    sequenceAdjunction.{u, v} orderedSphere.{u, v} tensorSphereMap.{u, v} M N f

/-- The inverse complete native Hom function retains every original module/operator inverse. -/
theorem VWAdjunction_homEquiv_symm_original
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) (g : X ⟶ W.{u, v}.obj Y) :
    (VWAdjunction.{u, v}.homEquiv X Y).symm g =
      (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.toAdjunction.homEquiv
        (moduleInduction.{u, v}.obj (sequentialModuleEquivalence.{u, v}.functor.obj X)) Y).symm
        ((moduleAdjunction.{u, v}.homEquiv (sequentialModuleEquivalence.{u, v}.functor.obj X)
          (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse.obj Y)).symm
          ((sequentialModuleEquivalence.{u, v}.toAdjunction.homEquiv X
            (moduleRestriction.{u, v}.obj
              (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse.obj Y))).symm g)) :=
  CategoryTheory.Adjunction.TripleComposition.inverse sequentialModuleEquivalence.{u, v}.toAdjunction
    moduleAdjunction.{u, v} SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.toAdjunction X Y g

/-- The whole original native counit is exactly the original three-stage counit composite. -/
theorem VWAdjunction_counit_original (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) :
    VWAdjunction.{u, v}.counit.app Y =
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor.map
        (moduleInduction.{u, v}.map
          (sequentialModuleEquivalence.{u, v}.toAdjunction.counit.app
            (moduleRestriction.{u, v}.obj
              (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse.obj Y)))) ≫
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.functor.map
        (moduleAdjunction.{u, v}.counit.app
          (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse.obj Y)) ≫
      SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.toAdjunction.counit.app Y :=
  CategoryTheory.Adjunction.TripleComposition.counit sequentialModuleEquivalence.{u, v}.toAdjunction
    moduleAdjunction.{u, v} SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.toAdjunction Y
/-- Both whole native Hom functions retain every original module/operator adjunction stage. -/
theorem VWAdjunction_homEquiv_original
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) (f : V.{u, v}.obj X ⟶ Y) :
    VWAdjunction.{u, v}.homEquiv X Y f =
      sequentialModuleEquivalence.{u, v}.toAdjunction.homEquiv X
        (moduleRestriction.{u, v}.obj
          (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse.obj Y))
        (moduleAdjunction.{u, v}.homEquiv (sequentialModuleEquivalence.{u, v}.functor.obj X)
          (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.inverse.obj Y)
          (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.toAdjunction.homEquiv
            (moduleInduction.{u, v}.obj (sequentialModuleEquivalence.{u, v}.functor.obj X)) Y f)) := by
  change ((sequentialModuleEquivalence.{u, v}.toAdjunction.comp moduleAdjunction.{u, v}).comp
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.toAdjunction).homEquiv X Y f = _
  rw [Adjunction.comp_homEquiv, Adjunction.comp_homEquiv]
  rfl

/-- Both complete inverse laws retain the original native source and target transformations. -/
theorem VWAdjunction_homEquiv_inverses
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) :
    (∀ f : V.{u, v}.obj X ⟶ Y,
      (VWAdjunction.{u, v}.homEquiv X Y).symm (VWAdjunction.{u, v}.homEquiv X Y f) = f) ∧
    (∀ g : X ⟶ W.{u, v}.obj Y,
      VWAdjunction.{u, v}.homEquiv X Y ((VWAdjunction.{u, v}.homEquiv X Y).symm g) = g) :=
  ⟨(VWAdjunction.{u, v}.homEquiv X Y).symm_apply_apply,
    (VWAdjunction.{u, v}.homEquiv X Y).apply_symm_apply⟩

/-- Every native source arrow retains the complete forward Hom naturality square. -/
theorem VWAdjunction_homEquiv_source
    {X X' : NativeIndexKanComposition.SequentialCarrier.{u, v}} (f : X ⟶ X')
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) (g : V.{u, v}.obj X' ⟶ Y) :
    VWAdjunction.{u, v}.homEquiv X Y (V.{u, v}.map f ≫ g) =
      f ≫ VWAdjunction.{u, v}.homEquiv X' Y g :=
  VWAdjunction.{u, v}.homEquiv_naturality_left f g

/-- Every native target arrow retains the complete forward Hom naturality square. -/
theorem VWAdjunction_homEquiv_target
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    {Y Y' : NativeIndexKanComposition.SymmetricCarrier.{u, v}} (f : Y ⟶ Y')
    (g : V.{u, v}.obj X ⟶ Y) :
    VWAdjunction.{u, v}.homEquiv X Y' (g ≫ f) =
      VWAdjunction.{u, v}.homEquiv X Y g ≫ W.{u, v}.map f :=
  VWAdjunction.{u, v}.homEquiv_naturality_right g f

/-- The entire original native unit is the three original module/operator unit maps. -/
theorem VWAdjunction_unit_original (X : NativeIndexKanComposition.SequentialCarrier.{u, v}) :
    VWAdjunction.{u, v}.unit.app X =
      sequentialModuleEquivalence.{u, v}.toAdjunction.unit.app X ≫
        sequentialModuleEquivalence.{u, v}.inverse.map
          (moduleAdjunction.{u, v}.unit.app (sequentialModuleEquivalence.{u, v}.functor.obj X)) ≫
        sequentialModuleEquivalence.{u, v}.inverse.map
          (moduleRestriction.{u, v}.map
            (SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.toAdjunction.unit.app
              (moduleInduction.{u, v}.obj (sequentialModuleEquivalence.{u, v}.functor.obj X)))) := by
  change ((sequentialModuleEquivalence.{u, v}.toAdjunction.comp moduleAdjunction.{u, v}).comp
    SymmetricModulePresentation.moduleOperatorEquivalence.{u, v}.toAdjunction).unit.app X = _
  rw [Adjunction.comp_unit_app, Adjunction.comp_unit_app]
  exact Category.assoc _ _ _

/-- Both complete original native adjunction triangles hold on every source and target. -/
theorem VWAdjunction_triangles_original
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) :
    V.{u, v}.map (VWAdjunction.{u, v}.unit.app X) ≫
      VWAdjunction.{u, v}.counit.app (V.{u, v}.obj X) = 𝟙 (V.{u, v}.obj X) ∧
    VWAdjunction.{u, v}.unit.app (W.{u, v}.obj Y) ≫
      W.{u, v}.map (VWAdjunction.{u, v}.counit.app Y) = 𝟙 (W.{u, v}.obj Y) :=
  ⟨VWAdjunction.{u, v}.left_triangle_components X,
    VWAdjunction.{u, v}.right_triangle_components Y⟩

/-- The full original module inverse uses both actual inverse Hom functions. -/
theorem moduleAdjunction_homEquiv_symm_original
    (M : Mod (CategoryTheory.Sequence PointedCGWH.{u, v}) orderedSphere.{u, v})
    (N : Mod SymmetricSequence.{u, v} sphereSequence.{u, v})
    (g : M ⟶ moduleRestriction.{u, v}.obj N) :
    (moduleAdjunction.{u, v}.homEquiv M N).symm g =
      (Mod.ExtensionOfScalars.homEquiv tensorSphereMap.{u, v}
        ((Functor.mapMod G.{u, v} orderedSphere.{u, v}).obj M) N).symm
        (((Mod.MonoidalAdjunction.adjunction sequenceAdjunction.{u, v} orderedSphere.{u, v}).homEquiv M
          ((Mod.ExtensionOfScalars.restriction tensorSphereMap.{u, v}).obj N)).symm g) :=
  CategoryTheory.Mod.MonoidalAdjunction.extensionOfScalarsAdjunction_homEquiv_symm
    sequenceAdjunction.{u, v} orderedSphere.{u, v} tensorSphereMap.{u, v} M N g

/-- Every original source map retains the complete inverse Hom naturality equation. -/
theorem VWAdjunction_inverse_source
    {X X' : NativeIndexKanComposition.SequentialCarrier.{u, v}} (f : X ⟶ X')
    (Y : NativeIndexKanComposition.SymmetricCarrier.{u, v}) (g : X' ⟶ W.{u, v}.obj Y) :
    (VWAdjunction.{u, v}.homEquiv X Y).symm (f ≫ g) =
      V.{u, v}.map f ≫ (VWAdjunction.{u, v}.homEquiv X' Y).symm g :=
  VWAdjunction.{u, v}.homEquiv_naturality_left_symm f g

/-- Every original target map retains the complete inverse Hom naturality equation. -/
theorem VWAdjunction_inverse_target
    (X : NativeIndexKanComposition.SequentialCarrier.{u, v})
    {Y Y' : NativeIndexKanComposition.SymmetricCarrier.{u, v}} (f : Y ⟶ Y')
    (g : X ⟶ W.{u, v}.obj Y) :
    (VWAdjunction.{u, v}.homEquiv X Y').symm (g ≫ W.{u, v}.map f) =
      (VWAdjunction.{u, v}.homEquiv X Y).symm g ≫ f :=
  VWAdjunction.{u, v}.homEquiv_naturality_right_symm g f

/-- Every original source map retains the complete actual native unit square. -/
theorem VWAdjunction_unit_naturality
    {X X' : NativeIndexKanComposition.SequentialCarrier.{u, v}} (f : X ⟶ X') :
    f ≫ VWAdjunction.{u, v}.unit.app X' =
      VWAdjunction.{u, v}.unit.app X ≫ W.{u, v}.map (V.{u, v}.map f) :=
  VWAdjunction.{u, v}.unit.naturality f

/-- Every original target map retains the complete actual native counit square. -/
theorem VWAdjunction_counit_naturality
    {Y Y' : NativeIndexKanComposition.SymmetricCarrier.{u, v}} (f : Y ⟶ Y') :
    V.{u, v}.map (W.{u, v}.map f) ≫ VWAdjunction.{u, v}.counit.app Y' =
      VWAdjunction.{u, v}.counit.app Y ≫ f :=
  VWAdjunction.{u, v}.counit.naturality f
end PointedCGWH.Spectra.SequentialSymmetricInductionComparison
