/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.Spectra.Orthogonal.SphereModuleStructure
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceIndexRecovery
public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceOperatorMorphism
public import MathlibExt.CategoryTheory.Enriched.Monoidal.DayConvolution.ExternalRightModuleCorrespondence

/-!
# The actual right sphere modules of native orthogonal diagrams

The source carrier is the stock category of right modules over the continuous
representation-sphere Day monoid. Restriction along the original delta and
the action of the original nu construct such a module from every native
operator diagram. Conversely, the complete stock action, extracted as a
genuine external transformation, supplies the unit and associative equations
of the native coend reconstruction.

These constructions use the maps of MMSS Definition 1.9, Proposition 1.10
and the proof of Theorem 2.2 in Section 23 of *Model categories of diagram
spectra*, December 30, 1999 preprint, pages 8–9 and 63. They retain the full
continuous isometry Hom objects, all source and sphere degrees, and both
native universe parameters. The unit and counit for the bundled categories
are constructed in `CanonicalSourceRightModuleEquivalence`.
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

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleActions

/-- The actual continuous orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original block-sum monoidal structure on the orthogonal index. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The genuine continuous enriched structure on the orthogonal index. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original continuous block-exchange symmetry. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- The actual enriched Day monoidal structure on orthogonal diagrams. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The original representation-sphere monoid in the enriched Day category. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}

attribute [local instance] Enriched.prodCategory
attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

open EnrichedDayKernel.ExternalRightModule

/-- The complete genuine native operator-functor carrier. -/
abbrev NativeDiagram :=
  EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalOperatorIndex.{u, v}

/-- The original stock right modules over the actual representation-sphere Day monoid. -/
abbrev SourceModule := NativeSphereModule.Carrier.{u, v}

/-- An action transformation for the original orthogonal sphere coefficient functor. -/
abbrev SourceTransformation (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  Transformation OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v} X

/-- The original unit law for a source action transformation. -/
abbrev SourceUnit (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
    (t : SourceTransformation X) :=
  SourceUnitLaw OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v} X t

/-- The original associativity law for a source action transformation. -/
abbrev SourceAssoc (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
    (t : SourceTransformation X) :=
  SourceAssocLaw OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    orthogonalSphereMonoidalData.{u, v} X t

/-- The native orthogonal diagram reconstructed from a lawful source action. -/
def reconstruct (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
    (t : SourceTransformation X) (hu : SourceUnit X t) (ha : SourceAssoc X t) :
    NativeDiagram.{u, v} :=
  CanonicalSourceOperatorFunctor.reverseFunctor X t hu ha

/-- The native diagram map reconstructed from a map of lawful source actions. -/
def reconstructMap (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
    (t : SourceTransformation X) (hu : SourceUnit X t) (ha : SourceAssoc X t)
    (Y : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
    (s : SourceTransformation Y) (hv : SourceUnit Y s) (hb : SourceAssoc Y s)
    (q : X ⟶ Y)
    (hq : TransformationComm OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X Y t s q) : reconstruct X t hu ha ⟶ reconstruct Y s hv hb :=
  CanonicalSourceOperatorMorphism.reverseMap X t hu ha Y s hv hb q hq

/-- Restriction and the original sphere action give an actual bundled stock right module. -/
def toModule (F : NativeDiagram.{u, v}) : SourceModule.{u, v} :=
  rightModule OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    ((restrictionFunctor.{u, v}).obj F) (sphereTransformation.{u, v} F)
    (CanonicalSourceUnitCompatibility.original_source_unit F)
    (CanonicalSourceCoefficientCompatibility.original_source_assoc F)

/-- The entire source I-space is the original restriction, including its Hom-map function. -/
theorem toModule_X (F : NativeDiagram.{u, v}) :
    (toModule F).X = (restrictionFunctor.{u, v}).obj F := rfl

/-- The stock action is the actual full Day descent of the original sphere transformation. -/
theorem toModule_action (F : NativeDiagram.{u, v}) :
    (toModule F).action =
      descend OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
        ((restrictionFunctor.{u, v}).obj F) (sphereTransformation.{u, v} F) := rfl

/-- Extraction preserves the whole original genuine sphere transformation. -/
theorem toModule_external (F : NativeDiagram.{u, v}) :
    NativeSphereModule.externalSphereTransformation (toModule F) =
      sphereTransformation.{u, v} F :=
  external_descend OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F)
    (sphereTransformation.{u, v} F)

/-- Every source structure map is the original nu action on the entire sphere coefficient. -/
theorem toModule_sphereComponent (F : NativeDiagram.{u, v}) (n a : OrthogonalIndex) :
    NativeSphereModule.sphereComponent (toModule F) n a = sphereAction.{u, v} F n a := by
  have h := congrArg (fun t => (eHomEquiv PointedCGWH.{u, v}).symm (t.app (n, a)))
    (toModule_external F)
  exact h.trans (sphereTransformation_component.{u, v} F (n, a))

/-- Every original continuous index action is retained by the bundled source module. -/
theorem toModule_indexMap (F : NativeDiagram.{u, v}) (n k : OrthogonalIndex) :
    (toModule F).X.toEnrichedFunctor.map n k = OrthogonalOperatorIndex.delta.{u, v} n k ≫
      F.toEnrichedFunctor.map (OrthogonalOperatorIndex.ofIndex.{u, v} n)
        (OrthogonalOperatorIndex.ofIndex.{u, v} k) :=
  restrictionFunctor_full_map.{u, v} F n k

/-- The extracted stock action satisfies the exact original source unit equation. -/
theorem module_source_unit (M : SourceModule.{u, v}) :
    SourceUnitLaw OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} M.X
      (NativeSphereModule.externalSphereTransformation M) :=
  stock_external_unit OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} M

/-- The extracted stock action satisfies the whole original external associativity equation. -/
theorem module_source_assoc (M : SourceModule.{u, v}) :
    SourceAssocLaw OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} M.X
      (NativeSphereModule.externalSphereTransformation M) :=
  stock_external_assoc OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} M

/-- The primitive source unit in the exact original native sphere-component type. -/
theorem module_sphere_unit (M : SourceModule.{u, v}) (n : OrthogonalIndex) :
    (M.X.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.epsilon) ≫
      NativeSphereModule.sphereComponent M n 0 ≫
      M.X.toEnrichedFunctor.toOrdinaryFunctor.map (ρ_ n).hom =
      (ρ_ (M.X.toEnrichedFunctor.obj n)).hom := module_source_unit M n

/-- The primitive source associativity in the exact original native component types. -/
theorem module_sphere_assoc (M : SourceModule.{u, v}) (n a b : OrthogonalIndex) :
    (α_ (M.X.toEnrichedFunctor.obj n) (PointedCGWH.orthogonalSphere.{u, v} a)
      (PointedCGWH.orthogonalSphere.{u, v} b)).inv ≫
      (NativeSphereModule.sphereComponent M n a ▷ PointedCGWH.orthogonalSphere.{u, v} b) ≫
      NativeSphereModule.sphereComponent M (n + a) b =
      (M.X.toEnrichedFunctor.obj n ◁ orthogonalSphereMonoidalData.{u, v}.mu a b) ≫
      NativeSphereModule.sphereComponent M n (a + b) ≫
      M.X.toEnrichedFunctor.toOrdinaryFunctor.map (α_ n a b).inv := module_source_assoc M n a b

/-- The actual stock source module reconstructs the entire genuine native operator functor. -/
def fromModule (M : SourceModule.{u, v}) : NativeDiagram.{u, v} :=
  reconstruct M.X
    (NativeSphereModule.externalSphereTransformation M)
    (module_source_unit M) (module_source_assoc M)

/-- Every native value is the literal original module value. -/
theorem fromModule_obj (M : SourceModule.{u, v}) (n : OrthogonalIndex) :
    (fromModule M).toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      M.X.toEnrichedFunctor.obj n := rfl

/-- The native Hom-map function is the original complete mapped-coend supplier. -/
theorem fromModule_fullMap (M : SourceModule.{u, v}) :
    HEq (fromModule M).toEnrichedFunctor.map (fun (n k : OrthogonalOperatorIndex.{u, v}) =>
      reverseOperatorMapField.{u, v} M.X (NativeSphereModule.externalSphereTransformation M)
        n.asIndex k.asIndex) := by rfl

/-- Uncurrying reconstructs the actual complete coend action, without replacing its generators. -/
theorem fromModule_action (M : SourceModule.{u, v}) (n k : OrthogonalIndex) :
    MonoidalClosed.uncurry ((fromModule M).toEnrichedFunctor.map
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) (OrthogonalOperatorIndex.ofIndex.{u, v} k)) =
      reverseOperatorAction.{u, v} M.X (NativeSphereModule.externalSphereTransformation M) n k :=
  CanonicalSourceOperatorFunctor.reverseFunctor_action M.X
    (NativeSphereModule.externalSphereTransformation M)
    (module_sphere_unit M) (module_sphere_assoc M) n k

/-- Restriction recovers every original continuous module Hom action. -/
theorem fromModule_restriction_fullMap (M : SourceModule.{u, v}) :
    ((restrictionFunctor.{u, v}).obj (fromModule M)).toEnrichedFunctor.map =
      M.X.toEnrichedFunctor.map :=
  CanonicalSourceIndexRecovery.reverseFunctor_restriction_fullMap M.X
    (NativeSphereModule.externalSphereTransformation M)
    (module_sphere_unit M) (module_sphere_assoc M)

/-- The entire original source I-space, including all map fields, is recovered. -/
theorem fromModule_restriction (M : SourceModule.{u, v}) :
    (restrictionFunctor.{u, v}).obj (fromModule M) = M.X :=
  CanonicalSourceIndexRecovery.reverseFunctor_restriction M.X
    (NativeSphereModule.externalSphereTransformation M)
    (module_sphere_unit M) (module_sphere_assoc M)

/-- The native reconstructed sphere map is the complete original stock structure map. -/
theorem fromModule_sphereAction (M : SourceModule.{u, v}) (n a : OrthogonalIndex) :
    sphereAction.{u, v} (fromModule M) n a = NativeSphereModule.sphereComponent M n a :=
  CanonicalSourceIndexRecovery.reverseFunctor_sphereAction M.X
    (NativeSphereModule.externalSphereTransformation M)
    (module_sphere_unit M) (module_sphere_assoc M) n a

/-- Every stock module morphism preserves the original entire sphere coefficient action. -/
theorem module_morphism_sphere {M N : SourceModule.{u, v}} (q : M ⟶ N)
    (n a : OrthogonalIndex) :
    NativeSphereModule.sphereComponent M n a ≫ EnrichedFunctorCat.component q.hom (n + a) =
      (EnrichedFunctorCat.component q.hom n ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
        NativeSphereModule.sphereComponent N n a := by
  have hM : NativeSphereModule.sphereComponent M n a =
      sigma OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
        M.X M.action n a := NativeSphereModule.sphereComponent_day_point M n a
  have hN : NativeSphereModule.sphereComponent N n a =
      sigma OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
        N.X N.action n a := NativeSphereModule.sphereComponent_day_point N n a
  exact (congrArg (fun z => z ≫ EnrichedFunctorCat.component q.hom (n + a)) hM).trans
    ((stock_source_comm OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} q n a).trans
      (congrArg (fun z => (EnrichedFunctorCat.component q.hom n ⊗ₘ
        𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫ z) hN).symm)

private theorem native_transformation_comm {F G : NativeDiagram.{u, v}} (q : F ⟶ G) :
    TransformationComm OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
      ((restrictionFunctor.{u, v}).obj F) ((restrictionFunctor.{u, v}).obj G)
      (sphereTransformation F) (sphereTransformation G) ((restrictionFunctor.{u, v}).map q) := by
  intro n a
  have hF := sphereTransformation_component.{u, v} F (n, a)
  have hG := sphereTransformation_component.{u, v} G (n, a)
  have hn := restrictionFunctor_map_component.{u, v} q n
  have hk := restrictionFunctor_map_component.{u, v} q (n + a)
  have hf := (congrArg (fun z => z ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) hn).trans
    (tensorHom_id (EnrichedFunctorCat.component q (OrthogonalOperatorIndex.ofIndex.{u, v} n))
      (PointedCGWH.orthogonalSphere.{u, v} a))
  exact (congrArg₂ (fun f g => f ≫ g) hF hk).trans
    ((sphereAction_natural.{u, v} q n a).trans (congrArg₂ (fun f g => f ≫ g) hf hG).symm)

private theorem module_transformation_comm {M N : SourceModule.{u, v}} (q : M ⟶ N) :
    TransformationComm OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
      M.X N.X (NativeSphereModule.externalSphereTransformation M)
      (NativeSphereModule.externalSphereTransformation N) q.hom := by
  intro n a
  exact module_morphism_sphere q n a

/-- An original native transformation descends to an actual sphere-module morphism. -/
def toModuleMap {F G : NativeDiagram.{u, v}} (q : F ⟶ G) : toModule F ⟶ toModule G :=
  homOfTransformation OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    ((restrictionFunctor.{u, v}).obj F) ((restrictionFunctor.{u, v}).obj G)
    (sphereTransformation.{u, v} F) (sphereTransformation.{u, v} G)
    (CanonicalSourceUnitCompatibility.original_source_unit F)
    (CanonicalSourceCoefficientCompatibility.original_source_assoc F)
    (CanonicalSourceUnitCompatibility.original_source_unit G)
    (CanonicalSourceCoefficientCompatibility.original_source_assoc G)
    ((restrictionFunctor.{u, v}).map q) (by exact native_transformation_comm q)

/-- The module morphism is the actual complete original restriction map. -/
theorem toModuleMap_hom {F G : NativeDiagram.{u, v}} (q : F ⟶ G) :
    (toModuleMap q).hom = (restrictionFunctor.{u, v}).map q := rfl

/-- Every original source component of a module map is unchanged. -/
theorem toModuleMap_component {F G : NativeDiagram.{u, v}} (q : F ⟶ G)
    (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (toModuleMap q).hom n =
      EnrichedFunctorCat.component q (OrthogonalOperatorIndex.ofIndex.{u, v} n) :=
  restrictionFunctor_map_component.{u, v} q n

/-- Every stock sphere-module morphism reconstructs a genuine native transformation. -/
def fromModuleMap {M N : SourceModule.{u, v}} (q : M ⟶ N) : fromModule M ⟶ fromModule N :=
  reconstructMap M.X
    (NativeSphereModule.externalSphereTransformation M)
    (module_source_unit M) (module_source_assoc M)
    N.X (NativeSphereModule.externalSphereTransformation N)
    (module_source_unit N) (module_source_assoc N) q.hom (by exact module_transformation_comm q)

/-- Every native component is the original component of the unchanged stock module morphism. -/
theorem fromModuleMap_component {M N : SourceModule.{u, v}} (q : M ⟶ N)
    (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (fromModuleMap q) (OrthogonalOperatorIndex.ofIndex.{u, v} n) =
      EnrichedFunctorCat.component q.hom n :=
  CanonicalSourceOperatorMorphism.reverseMap_component M.X
    (NativeSphereModule.externalSphereTransformation M)
    (module_sphere_unit M) (module_sphere_assoc M)
    N.X (NativeSphereModule.externalSphereTransformation N)
    (module_sphere_unit N) (module_sphere_assoc N) q.hom (module_morphism_sphere q) n

/-- The entire reconstructed component function consists of the original source components. -/
theorem fromModuleMap_fullApp {M N : SourceModule.{u, v}} (q : M ⟶ N) :
    HEq (fromModuleMap q).app (fun (n : OrthogonalOperatorIndex.{u, v}) =>
      eHomEquiv PointedCGWH.{u, v} (EnrichedFunctorCat.component q.hom n.asIndex)) := by
  unfold fromModuleMap reconstructMap
  rw [CanonicalSourceOperatorMorphism.reverseMap_fullApp]

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleActions
