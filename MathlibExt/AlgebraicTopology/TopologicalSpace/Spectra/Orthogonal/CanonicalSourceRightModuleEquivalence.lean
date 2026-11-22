/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleActions
public import MathlibExt.CategoryTheory.Enriched.FunctorCategoryIso
public import MathlibExt.CategoryTheory.Enriched.RightModuleSourceIso
public import MathlibExt.CategoryTheory.Monoidal.RightModuleFreeCoefficient

/-!
# The complete native orthogonal right-sphere-module equivalence

Every stock right module over the original continuous sphere Day monoid
reconstructs an operator diagram by its whole coend action. Restriction and
the original sphere inclusion recover the entire source action. The native
round trip recovers the whole enriched operator Hom-map function. The source
round trip is an isomorphism of the original stock modules, with both actual
module arrows and identity maps on all level spaces.

This is the carrier part of MMSS Theorem 2.2 and its proof on page 63 of the
December 30, 1999 preprint of *Model categories of diagram spectra*. The
continuous Hom/composition/unit comparison with its orthogonal `I_S`
presentation is the existing `CanonicalSourceThomComparison.diagramEquivalence`.
The equivalence here uses actual source modules as its second category; it
does not construct an equivalence from a native reconstruction endofunctor.
-/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section
universe u v

open CategoryTheory Limits MonoidalCategory
open CategoryTheory.Spectra CategoryTheory.Enriched.SphereOperator
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open scoped MonoidalClosed

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleEquivalence.Internal

universe uV vV uI vI

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

variable {V : Type uV} [Category.{vV} V] [MonoidalCategory V]
  [SymmetricCategory V] [MonoidalClosed V]
  {I : Type uI} [Category.{vI} I] [MonoidalCategory I]
  [EnrichedOrdinaryCategory V I] [HasColimitsOfSize.{uI, uI} V]
  (d : EnrichedMonoidalCategoryData V I) (S : EnrichedFunctor V I V)
  (L : EnrichedFunctor.LaxMonoidalData d
    (MonoidalClosed.enrichedMonoidalCategoryDataSelf V) S)

open EnrichedDayKernel.ExternalRightModule

/-- Full source squares produce both arrows of the actual stock-module isomorphism. -/
def isoOfSourceComm :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    ∀ (M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (e : M.X ≅ N.X), SourceComm d S M.X N.X M.action N.action e.hom → (M ≅ N) :=
  EnrichedDayKernel.ExternalRightModule.isoOfSourceComm d S L

/-- The complete forward map is the supplied original diagram map. -/
theorem isoOfSourceComm_hom :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    ∀ (M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (e : M.X ≅ N.X) (h : SourceComm d S M.X N.X M.action N.action e.hom),
      (isoOfSourceComm d S L M N e h).hom.hom = e.hom :=
  EnrichedDayKernel.ExternalRightModule.isoOfSourceComm_hom d S L

/-- The complete inverse map is the supplied original inverse diagram map. -/
theorem isoOfSourceComm_inv :
    letI := EnrichedDayKernel.ColimitMonoidal.monoidalCategory d
    letI := EnrichedDayKernel.LaxMonoid.monObj d S L
    ∀ (M N : CommutativeModuleConversion.RightModule (⟨S⟩ : EnrichedFunctorCat V I))
      (e : M.X ≅ N.X) (h : SourceComm d S M.X N.X M.action N.action e.hom),
      (isoOfSourceComm d S L M N e h).inv.hom = e.inv :=
  EnrichedDayKernel.ExternalRightModule.isoOfSourceComm_inv d S L

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleEquivalence.Internal

namespace PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleEquivalence

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

open CanonicalSourceRightModuleActions EnrichedDayKernel.ExternalRightModule

private theorem reverseFunctor_congr
    (X : EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex)
    (t s : Transformation OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} X)
    (hu : SourceUnitLaw OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} X t)
    (ha : SourceAssocLaw OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} X t)
    (hv : SourceUnitLaw OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} X s)
    (hb : SourceAssocLaw OrthogonalIndex.enrichedMonoidalData.{u, v}
      orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v} X s)
    (h : t = s) : CanonicalSourceOperatorFunctor.reverseFunctor X t hu ha =
      CanonicalSourceOperatorFunctor.reverseFunctor X s hv hb := by
  cases h
  rfl

/-- The original native/source construction preserves every identity and composite. -/
def toModuleFunctor : NativeDiagram.{u, v} ⥤ SourceModule.{u, v} where
  obj := toModule
  map := toModuleMap
  map_id F := by
    apply Mod.Hom.ext
    exact (restrictionFunctor.{u, v}).map_id F
  map_comp q r := by
    apply Mod.Hom.ext
    exact (restrictionFunctor.{u, v}).map_comp q r

/-- The source's whole coend reconstruction is functorial on all stock module morphisms. -/
def fromModuleFunctor : SourceModule.{u, v} ⥤ NativeDiagram.{u, v} where
  obj := fromModule
  map := fromModuleMap
  map_id M := by
    apply EnrichedFunctorCat.hom_ext
    intro n
    change EnrichedFunctorCat.component (fromModuleMap (𝟙 M))
      (OrthogonalOperatorIndex.ofIndex.{u, v} n.asIndex) = _
    rw [fromModuleMap_component]
    exact (EnrichedFunctorCat.component_id M.X n.asIndex).trans
      (EnrichedFunctorCat.component_id (fromModule M) n).symm
  map_comp q r := by
    apply EnrichedFunctorCat.hom_ext
    intro n
    have hl := fromModuleMap_component (q ≫ r) n.asIndex
    have hr := congrArg₂ (fun f g => f ≫ g)
      (fromModuleMap_component q n.asIndex) (fromModuleMap_component r n.asIndex)
    have hc := EnrichedFunctorCat.component_comp (fromModuleMap q) (fromModuleMap r) n
    exact hl.trans ((EnrichedFunctorCat.component_comp q.hom r.hom n.asIndex).trans
      (hc.trans hr).symm)

/-- The native-to-source functor retains every whole original restriction map. -/
theorem toModuleFunctor_map_hom {F G : NativeDiagram.{u, v}} (q : F ⟶ G) :
    (toModuleFunctor.map q).hom = (restrictionFunctor.{u, v}).map q := rfl

/-- The source-to-native functor retains every component of the original module morphism. -/
theorem fromModuleFunctor_map_component {M N : SourceModule.{u, v}} (q : M ⟶ N)
    (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (fromModuleFunctor.map q)
      (OrthogonalOperatorIndex.ofIndex.{u, v} n) = EnrichedFunctorCat.component q.hom n :=
  fromModuleMap_component q n

/-- Both native constructions recover the whole original operator Hom-map function. -/
theorem nativeRoundTrip_fullMap (F : NativeDiagram.{u, v}) :
    (fromModule (toModule F)).toEnrichedFunctor.map = F.toEnrichedFunctor.map := by
  funext n k
  have h := congrArg
    (fun t : Transformation OrthogonalIndex.enrichedMonoidalData.{u, v}
        orthogonalSphereFunctor.{u, v} ((restrictionFunctor.{u, v}).obj F) =>
      reverseOperatorMapField.{u, v} ((restrictionFunctor.{u, v}).obj F) t
        n.asIndex k.asIndex) (toModule_external F)
  exact h.trans (reverseOperatorMapField_original.{u, v} F n.asIndex k.asIndex)

/-- Both native constructions recover the original bundled enriched functor itself. -/
theorem nativeRoundTrip_eq (F : NativeDiagram.{u, v}) : fromModule (toModule F) = F := by
  have h := reverseFunctor_congr ((restrictionFunctor.{u, v}).obj F)
    (NativeSphereModule.externalSphereTransformation (toModule F)) (sphereTransformation F)
    (module_source_unit (toModule F)) (module_source_assoc (toModule F))
    (CanonicalSourceUnitCompatibility.original_source_unit F)
    (CanonicalSourceCoefficientCompatibility.original_source_assoc F) (toModule_external F)
  exact h.trans (CanonicalSourceOperatorFunctor.originalReverseFunctor_eq F)

/-- Both source constructions recover the entire original source enriched I-space. -/
theorem sourceRoundTrip_X (M : SourceModule.{u, v}) : (toModule (fromModule M)).X = M.X :=
  fromModule_restriction M

/-- Both source constructions recover every original right sphere structure map. -/
theorem sourceRoundTrip_sphereComponent (M : SourceModule.{u, v}) (n a : OrthogonalIndex) :
    NativeSphereModule.sphereComponent (toModule (fromModule M)) n a =
      NativeSphereModule.sphereComponent M n a :=
  (toModule_sphereComponent (fromModule M) n a).trans (fromModule_sphereAction M n a)

/-- The original native round trip has literal identity maps on every unchanged level space. -/
def nativeRoundTripIso (F : NativeDiagram.{u, v}) : fromModule (toModule F) ≅ F :=
  EnrichedFunctorCat.isoOfComponents (fromModule (toModule F)) F
    (fun n => Iso.refl (F.toEnrichedFunctor.obj n)) (by
      intro n k
      have h := congrArg MonoidalClosed.uncurry
        (congrFun (congrFun (nativeRoundTrip_fullMap F) n) k)
      have hr := (congrArg (fun f => f ≫ MonoidalClosed.uncurry (F.toEnrichedFunctor.map n k))
        (id_tensorHom_id (F.toEnrichedFunctor.obj n) (n ⟶[PointedCGWH.{u, v}] k))).trans
          (Category.id_comp _)
      exact (Category.comp_id _).trans (h.trans hr.symm))

/-- Every forward native comparison component is the original identity. -/
theorem nativeRoundTripIso_hom_component (F : NativeDiagram.{u, v})
    (n : OrthogonalOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (nativeRoundTripIso F).hom n =
      𝟙 (F.toEnrichedFunctor.obj n) :=
  EnrichedFunctorCat.isoOfComponents_hom_component _ _ _ _ n

/-- Every inverse native comparison component is the original identity. -/
theorem nativeRoundTripIso_inv_component (F : NativeDiagram.{u, v})
    (n : OrthogonalOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (nativeRoundTripIso F).inv n =
      𝟙 (F.toEnrichedFunctor.obj n) :=
  EnrichedFunctorCat.isoOfComponents_inv_component _ _ _ _ n

/-- The entire source diagram round trip retains the original continuous Hom action. -/
def sourceDiagramRoundTripIso (M : SourceModule.{u, v}) : (toModule (fromModule M)).X ≅ M.X :=
  EnrichedFunctorCat.isoOfComponents (toModule (fromModule M)).X M.X
    (fun n => Iso.refl (M.X.toEnrichedFunctor.obj n)) (by
      intro n k
      have h := congrArg MonoidalClosed.uncurry
        (congrFun (congrFun (fromModule_restriction_fullMap M) n) k)
      have hr := (congrArg (fun f => f ≫ MonoidalClosed.uncurry (M.X.toEnrichedFunctor.map n k))
        (id_tensorHom_id (M.X.toEnrichedFunctor.obj n) (n ⟶[PointedCGWH.{u, v}] k))).trans
          (Category.id_comp _)
      exact (Category.comp_id _).trans (h.trans hr.symm))

/-- Every forward source diagram comparison has the original identity component. -/
theorem sourceDiagramRoundTripIso_hom_component (M : SourceModule.{u, v}) (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (sourceDiagramRoundTripIso M).hom n =
      𝟙 (M.X.toEnrichedFunctor.obj n) :=
  EnrichedFunctorCat.isoOfComponents_hom_component _ _ _ _ n

/-- Every inverse source diagram comparison has the original identity component. -/
theorem sourceDiagramRoundTripIso_inv_component (M : SourceModule.{u, v}) (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (sourceDiagramRoundTripIso M).inv n =
      𝟙 (M.X.toEnrichedFunctor.obj n) :=
  EnrichedFunctorCat.isoOfComponents_inv_component _ _ _ _ n

/-- The identity-component comparison preserves the full original external action. -/
theorem sourceRoundTrip_sourceComm (M : SourceModule.{u, v}) :
    SourceComm OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
      (toModule (fromModule M)).X M.X (toModule (fromModule M)).action M.action
      (sourceDiagramRoundTripIso M).hom := by
  intro n a
  let p := sigma OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    (toModule (fromModule M)).X (toModule (fromModule M)).action n a
  let q := sigma OrthogonalIndex.enrichedMonoidalData.{u, v} orthogonalSphereFunctor.{u, v}
    M.X M.action n a
  have hp : p = q :=
    (NativeSphereModule.sphereComponent_day_point (toModule (fromModule M)) n a).symm.trans
      ((sourceRoundTrip_sphereComponent M n a).trans
        (NativeSphereModule.sphereComponent_day_point M n a))
  have hn := sourceDiagramRoundTripIso_hom_component M n
  have hk := sourceDiagramRoundTripIso_hom_component M (n + a)
  have ht : (EnrichedFunctorCat.component (sourceDiagramRoundTripIso M).hom n ⊗ₘ
      𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) =
      𝟙 (M.X.toEnrichedFunctor.obj n ⊗ PointedCGWH.orthogonalSphere.{u, v} a) :=
    (congrArg (fun f => f ⊗ₘ 𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) hn).trans
      (id_tensorHom_id _ _)
  exact ((congrArg (fun f => p ≫ f) hk).trans (Category.comp_id p)).trans
    (hp.trans ((Category.id_comp q).symm.trans (congrArg (fun f => f ≫ q) ht).symm))

/-- The source round trip is an actual isomorphism in the original stock module category. -/
def sourceRoundTripIso (M : SourceModule.{u, v}) : toModule (fromModule M) ≅ M :=
  Internal.isoOfSourceComm OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    (toModule (fromModule M)) M (sourceDiagramRoundTripIso M) (sourceRoundTrip_sourceComm M)

/-- The actual stock comparison satisfies the entire original Day action equation. -/
theorem sourceRoundTrip_linear (M : SourceModule.{u, v}) :
    (toModule (fromModule M)).action ≫ (sourceRoundTripIso M).hom.hom =
      ((sourceRoundTripIso M).hom.hom ▷ sphereISpace.{u, v}) ≫ M.action :=
  CommutativeModuleConversion.RightModule.comm (sourceRoundTripIso M).hom

/-- The forward stock comparison is the same whole original enriched diagram comparison. -/
theorem sourceRoundTripIso_hom_hom (M : SourceModule.{u, v}) :
    (sourceRoundTripIso M).hom.hom = (sourceDiagramRoundTripIso M).hom :=
  Internal.isoOfSourceComm_hom OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    (toModule (fromModule M)) M (sourceDiagramRoundTripIso M) (sourceRoundTrip_sourceComm M)

/-- The inverse stock comparison is the same whole inverse enriched diagram comparison. -/
theorem sourceRoundTripIso_inv_hom (M : SourceModule.{u, v}) :
    (sourceRoundTripIso M).inv.hom = (sourceDiagramRoundTripIso M).inv :=
  Internal.isoOfSourceComm_inv OrthogonalIndex.enrichedMonoidalData.{u, v}
    orthogonalSphereFunctor.{u, v} orthogonalSphereMonoidalData.{u, v}
    (toModule (fromModule M)) M (sourceDiagramRoundTripIso M) (sourceRoundTrip_sourceComm M)

/-- Every forward stock-module comparison retains the original identity at each level. -/
theorem sourceRoundTripIso_hom_component (M : SourceModule.{u, v}) (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (sourceRoundTripIso M).hom.hom n =
      𝟙 (M.X.toEnrichedFunctor.obj n) :=
  (congrArg (fun q => EnrichedFunctorCat.component q n) (sourceRoundTripIso_hom_hom M)).trans
    (sourceDiagramRoundTripIso_hom_component M n)

/-- Every inverse stock-module comparison retains the original identity at each level. -/
theorem sourceRoundTripIso_inv_component (M : SourceModule.{u, v}) (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (sourceRoundTripIso M).inv.hom n =
      𝟙 (M.X.toEnrichedFunctor.obj n) :=
  (congrArg (fun q => EnrichedFunctorCat.component q n) (sourceRoundTripIso_inv_hom M)).trans
    (sourceDiagramRoundTripIso_inv_component M n)

/-- Both original module comparison arrows preserve every original right sphere action. -/
theorem sourceRoundTripIso_inv_sphere (M : SourceModule.{u, v}) (n a : OrthogonalIndex) :
    NativeSphereModule.sphereComponent M n a ≫
        EnrichedFunctorCat.component (sourceRoundTripIso M).inv.hom (n + a) =
      (EnrichedFunctorCat.component (sourceRoundTripIso M).inv.hom n ⊗ₘ
        𝟙 (PointedCGWH.orthogonalSphere.{u, v} a)) ≫
      NativeSphereModule.sphereComponent (toModule (fromModule M)) n a :=
  module_morphism_sphere (sourceRoundTripIso M).inv n a

/-- The native morphism round trip conserves every entire original component. -/
theorem nativeRoundTrip_map_component {F G : NativeDiagram.{u, v}} (q : F ⟶ G)
    (n : OrthogonalOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component ((toModuleFunctor ⋙ fromModuleFunctor).map q) n =
      EnrichedFunctorCat.component q n :=
  (fromModuleMap_component (toModuleMap q) n.asIndex).trans (toModuleMap_component q n.asIndex)

/-- The source morphism round trip conserves every entire original module component. -/
theorem sourceRoundTrip_map_component {M N : SourceModule.{u, v}} (q : M ⟶ N)
    (n : OrthogonalIndex) :
    EnrichedFunctorCat.component ((fromModuleFunctor ⋙ toModuleFunctor).map q).hom n =
      EnrichedFunctorCat.component q.hom n :=
  (toModuleMap_component (fromModuleMap q) n).trans (fromModuleMap_component q n)

/-- The original identity-component native comparison is natural on all genuine transformations. -/
def unitIso : 𝟭 NativeDiagram.{u, v} ≅ toModuleFunctor ⋙ fromModuleFunctor :=
  NatIso.ofComponents (fun F => (nativeRoundTripIso F).symm) (by
    intro F G q
    change q ≫ (nativeRoundTripIso G).inv =
      (nativeRoundTripIso F).inv ≫ (toModuleFunctor ⋙ fromModuleFunctor).map q
    apply EnrichedFunctorCat.hom_ext
    intro n
    have hl := (EnrichedFunctorCat.component_comp q (nativeRoundTripIso G).inv n).trans
      ((congrArg (fun f => EnrichedFunctorCat.component q n ≫ f)
        (nativeRoundTripIso_inv_component G n)).trans (Category.comp_id _))
    have hr := (EnrichedFunctorCat.component_comp (nativeRoundTripIso F).inv
      ((toModuleFunctor ⋙ fromModuleFunctor).map q) n).trans
        ((congrArg₂ (fun f g => f ≫ g) (nativeRoundTripIso_inv_component F n)
          (nativeRoundTrip_map_component q n)).trans (Category.id_comp _))
    exact hl.trans hr.symm)

/-- The original stock-module comparison is natural on every entire original module morphism. -/
def counitIso : fromModuleFunctor ⋙ toModuleFunctor ≅ 𝟭 SourceModule.{u, v} :=
  NatIso.ofComponents sourceRoundTripIso (by
    intro M N q
    apply Mod.Hom.ext
    apply EnrichedFunctorCat.hom_ext
    intro n
    change EnrichedFunctorCat.component
      (((fromModuleFunctor ⋙ toModuleFunctor).map q).hom ≫ (sourceRoundTripIso N).hom.hom) n =
      EnrichedFunctorCat.component ((sourceRoundTripIso M).hom.hom ≫ q.hom) n
    rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
      sourceRoundTripIso_hom_component, sourceRoundTripIso_hom_component,
      sourceRoundTrip_map_component]
    change EnrichedFunctorCat.component q.hom n ≫ 𝟙 (N.X.toEnrichedFunctor.obj n) =
      𝟙 (M.X.toEnrichedFunctor.obj n) ≫ EnrichedFunctorCat.component q.hom n
    exact (Category.comp_id _).trans (Category.id_comp _).symm)

/-!
Component laws for the complete original native/source triangle.
-/
private theorem current_unit_component (F : NativeDiagram.{u, v})
    (n : OrthogonalOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (unitIso.hom.app F) n =
      𝟙 (F.toEnrichedFunctor.obj n) :=
  nativeRoundTripIso_inv_component F n

private theorem current_counit_component (M : SourceModule.{u, v})
    (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (counitIso.hom.app M).hom n =
      𝟙 (M.X.toEnrichedFunctor.obj n) :=
  sourceRoundTripIso_hom_component M n

private theorem current_mapped_unit_component (F : NativeDiagram.{u, v})
    (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (toModuleFunctor.map (unitIso.hom.app F)).hom n =
      𝟙 ((toModuleFunctor.obj F).X.toEnrichedFunctor.obj n) :=
  (toModuleMap_component (unitIso.hom.app F) n).trans
    (current_unit_component F (OrthogonalOperatorIndex.ofIndex.{u, v} n))

private theorem current_triangle_component (F : NativeDiagram.{u, v})
    (n : OrthogonalIndex) :
    EnrichedFunctorCat.component
        ((toModuleFunctor.map (unitIso.hom.app F)).hom ≫
          (counitIso.hom.app (toModuleFunctor.obj F)).hom) n =
      EnrichedFunctorCat.component (𝟙 (toModuleFunctor.obj F).X) n :=
  (EnrichedFunctorCat.component_comp _ _ n).trans
    ((congrArg₂ (fun f g => f ≫ g)
      (current_mapped_unit_component F n)
      (current_counit_component (toModuleFunctor.obj F) n)).trans
        ((Category.id_comp _).trans
          (EnrichedFunctorCat.component_id (toModuleFunctor.obj F).X n).symm))

private theorem original_functor_unitIso_comp (F : NativeDiagram.{u, v}) :
    toModuleFunctor.map (unitIso.hom.app F) ≫
        counitIso.hom.app (toModuleFunctor.obj F) = 𝟙 (toModuleFunctor.obj F) := by
  apply Mod.Hom.ext
  apply EnrichedFunctorCat.hom_ext
  intro n
  exact current_triangle_component F n

/-- The complete native/source equivalence has actual inverse functors and original module maps. -/
def equivalence : NativeDiagram.{u, v} ≌ NativeSphereModule.Carrier.{u, v} where
  functor := toModuleFunctor
  inverse := fromModuleFunctor
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp := by
    exact original_functor_unitIso_comp

/-- Every equivalence unit component is the original native identity. -/
theorem unit_hom_component (F : NativeDiagram.{u, v}) (n : OrthogonalOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (equivalence.unitIso.hom.app F) n =
      𝟙 (F.toEnrichedFunctor.obj n) := nativeRoundTripIso_inv_component F n

/-- Every inverse equivalence unit component is the original native identity. -/
theorem unit_inv_component (F : NativeDiagram.{u, v}) (n : OrthogonalOperatorIndex.{u, v}) :
    EnrichedFunctorCat.component (equivalence.unitIso.inv.app F) n =
      𝟙 (F.toEnrichedFunctor.obj n) := nativeRoundTripIso_hom_component F n

/-- Every equivalence counit component is the original source identity. -/
theorem counit_hom_component (M : SourceModule.{u, v}) (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (equivalence.counitIso.hom.app M).hom n =
      𝟙 (M.X.toEnrichedFunctor.obj n) := sourceRoundTripIso_hom_component M n

/-- Every inverse equivalence counit component is the original source identity. -/
theorem counit_inv_component (M : SourceModule.{u, v}) (n : OrthogonalIndex) :
    EnrichedFunctorCat.component (equivalence.counitIso.inv.app M).hom n =
      𝟙 (M.X.toEnrichedFunctor.obj n) := sourceRoundTripIso_inv_component M n

/-- Both full original source morphisms obey the source-side inverse law. -/
theorem source_morphism_inverse {M N : SourceModule.{u, v}} (q : M ⟶ N) :
    (equivalence.counitIso.inv.app M) ≫ (fromModuleFunctor ⋙ toModuleFunctor).map q ≫
      equivalence.counitIso.hom.app N = q := by
  apply Mod.Hom.ext
  apply EnrichedFunctorCat.hom_ext
  intro n
  change EnrichedFunctorCat.component
    ((equivalence.counitIso.inv.app M).hom ≫
      ((fromModuleFunctor ⋙ toModuleFunctor).map q).hom ≫
      (equivalence.counitIso.hom.app N).hom) n = EnrichedFunctorCat.component q.hom n
  rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
    counit_inv_component, counit_hom_component, sourceRoundTrip_map_component]
  change 𝟙 (M.X.toEnrichedFunctor.obj n) ≫ EnrichedFunctorCat.component q.hom n ≫
    𝟙 (N.X.toEnrichedFunctor.obj n) = EnrichedFunctorCat.component q.hom n
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- Both full original native morphisms obey the native-side inverse law. -/
theorem native_morphism_inverse {F G : NativeDiagram.{u, v}} (q : F ⟶ G) :
    equivalence.unitIso.hom.app F ≫ (toModuleFunctor ⋙ fromModuleFunctor).map q ≫
      equivalence.unitIso.inv.app G = q := by
  apply EnrichedFunctorCat.hom_ext
  intro n
  rw [EnrichedFunctorCat.component_comp, EnrichedFunctorCat.component_comp,
    unit_hom_component, unit_inv_component, nativeRoundTrip_map_component]
  change 𝟙 (F.toEnrichedFunctor.obj n) ≫ EnrichedFunctorCat.component q n ≫
    𝟙 (G.toEnrichedFunctor.obj n) = EnrichedFunctorCat.component q n
  exact (Category.id_comp _).trans (Category.comp_id _)

/-- The original source-side triangle retains the whole module morphism. -/
theorem source_triangle (F : NativeDiagram.{u, v}) :
    toModuleFunctor.map (equivalence.unitIso.hom.app F) ≫
      equivalence.counitIso.hom.app (toModuleFunctor.obj F) = 𝟙 (toModuleFunctor.obj F) :=
  equivalence.functor_unitIso_comp F

/-- The original native-side triangle retains the whole genuine enriched transformation. -/
theorem native_triangle (M : SourceModule.{u, v}) :
    equivalence.unitIso.hom.app (fromModuleFunctor.obj M) ≫
      fromModuleFunctor.map (equivalence.counitIso.hom.app M) = 𝟙 (fromModuleFunctor.obj M) := by
  apply EnrichedFunctorCat.hom_ext
  intro n
  have hf := fromModuleFunctor_map_component (equivalence.counitIso.hom.app M) n.asIndex
  have he := counit_hom_component M n.asIndex
  have hu := unit_hom_component (fromModuleFunctor.obj M) n
  have hc := EnrichedFunctorCat.component_comp
    (equivalence.unitIso.hom.app (fromModuleFunctor.obj M))
    (fromModuleFunctor.map (equivalence.counitIso.hom.app M)) n
  have h := hc.trans (congrArg₂ (fun f g => f ≫ g) hu (hf.trans he))
  have hid := Category.id_comp
    (𝟙 ((fromModuleFunctor.obj M).toEnrichedFunctor.obj n))
  exact h.trans (hid.trans (EnrichedFunctorCat.component_id (fromModuleFunctor.obj M) n).symm)

end PointedCGWH.Spectra.Orthogonal.CanonicalSourceRightModuleEquivalence
