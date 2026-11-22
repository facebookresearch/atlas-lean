/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.CategoryTheory.Enriched.ModuleMappingRFreeEvaluation
import MathlibExt.CategoryTheory.Enriched.FreeWeightedEnd
import MathlibExt.CategoryTheory.Enriched.FreeWeightedEndMap
import MathlibExt.Topology.Category.PointedCGWH.EnrichedMappingEnds
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.CanonicalSourceRightModuleEquivalence
import MathlibExt.AlgebraicTopology.TopologicalSpace.Spectra.Orthogonal.FunctionSpectrum.RightShift

/-!
# Original free-source values of orthogonal function spectra

The actual stock free right sphere module retains the full enriched free
I-space. The Mapping_R equalizer restricts along its original generator,
and the original free weighted end evaluates at its complete identity.
The result keeps the literal source order N(r tensor c). The actual index
block isometry then compares it with the right-shift value N(c tensor r).
All degrees and coefficient spaces remain unrestricted. The inherited
Mapping_R output-module action remains a separate source producer.
-/

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory MonoidalCategory BraidedCategory Limits
open CategoryTheory.Enriched CategoryTheory.EnrichedFunctorCat CategoryTheory.Spectra
open CategoryTheory.Spectra.OrthogonalSourceRightModule
open CategoryTheory.Enriched.SphereOperator
open scoped MonoidalClosed

universe u v

namespace PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSource

/-- The original continuous orthogonal index category. -/
local instance : Category.{v} OrthogonalIndex := OrthogonalIndex.category.{u, v}
/-- The original orthogonal index tensor structure. -/
local instance : MonoidalCategory OrthogonalIndex := OrthogonalIndex.monoidalCategory.{u, v}
/-- The original pointed enrichment of orthogonal indexing. -/
local instance : EnrichedOrdinaryCategory PointedCGWH.{u, v} OrthogonalIndex :=
  OrthogonalIndex.enrichedOrdinaryCategory.{u, v}
/-- The original block-swap symmetry of orthogonal indexing. -/
local instance : SymmetricCategory OrthogonalIndex := OrthogonalIndex.symmetricCategory.{u, v}
/-- The actual Day tensor structure on the original orthogonal I-spaces. -/
local instance : MonoidalCategory (EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex) :=
  OrthogonalDay.monoidalCategory.{u, v}
/-- The representation-sphere monoid in the original Day category. -/
local instance : MonObj sphereISpace.{u, v} := OrthogonalDay.sphereMonObj.{u, v}
local instance : HasLimitsOfSize.{0, 0} PointedCGWH.{u, v} :=
  PointedCGWH.EnrichedMapping.hasSmallLimits.{u, v}

attribute [local instance] MonoidalLeftAction.monoidalOppositeLeftAction

private abbrev d := OrthogonalIndex.enrichedMonoidalData.{u, v}
private abbrev b := OrthogonalIndex.enrichedSymmetricData.{u, v}
private abbrev S := orthogonalSphereFunctor.{u, v}
private abbrev L := orthogonalSphereMonoidalData.{u, v}

open CanonicalSourceRightModuleActions CanonicalSourceRightModuleEquivalence
open EnrichedDayKernel CategoryTheory.Enriched.ModuleMappingR

/-- Each original degree and arbitrary coefficient determines its actual
source free right module. -/
abbrev freeAt (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r X

/-- The source's complete free-function value retains the literal ordered translation. -/
def valueIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (N : SourceModule.{u, v}) (c : OrthogonalIndex) :
    value d.{u, v} b.{u, v} S.{u, v} L.{u, v} (freeAt r X) N c ≅
      (ihom X).obj (N.X.toEnrichedFunctor.obj (r + c)) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c

/-- The actual full native block isometry changes the source translation order. -/
def blockValueIso (r c : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (F : NativeDiagram.{u, v}) :
    (ihom X).obj ((toModule F).X.toEnrichedFunctor.obj (r + c)) ≅
      (ihom X).obj (F.toEnrichedFunctor.obj (OrthogonalOperatorIndex.ofIndex.{u, v} (c + r))) :=
  (ihom X).mapIso ((RightShift.bare F).mapIso (β_ r c))

/-- Every whole free-source value compares with the actual right-shift scalar cotensor value. -/
def rightShiftValueIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (F : NativeDiagram.{u, v}) (c : OrthogonalIndex) :
    value d.{u, v} b.{u, v} S.{u, v} L.{u, v} (freeAt r X) (toModule F) c ≅
      ((cotensor X).obj ((RightShift.shift r).obj F)).toEnrichedFunctor.obj
        (OrthogonalOperatorIndex.ofIndex.{u, v} c) :=
  valueIso r X (toModule F) c ≪≫ blockValueIso r c X F

/-- The actual original Mapping_R equalizer on the complete stock free right sphere module. -/
abbrev rawFunction (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (N : SourceModule.{u, v}) :
    EnrichedFunctorCat PointedCGWH.{u, v} OrthogonalIndex :=
  ModuleMappingR.diagram d.{u, v} b.{u, v} S.{u, v} L.{u, v} (freeAt r X) N

/-- Both full continuous index actions identify the genuine shift
with original right translation. -/
def bareShiftIso (r : OrthogonalIndex) (F : NativeDiagram.{u, v}) :
    (toModule ((RightShift.shift r).obj F)).X ≅
      EnrichedDayKernel.Closed.translatedTarget d.{u, v} (toModule F).X r :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.shiftedRestrictionIso PointedCGWH.isSeparator_tensorUnit
    d.{u, v} S.{u, v} L.{u, v} F r

/-- The full raw free-function diagram compares with the actual scalar cotensor of right shift. -/
def rightShiftDiagramIso (r : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (F : NativeDiagram.{u, v}) :
    CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.RightShiftRestrictionIsoType
      (J := OrthogonalOperatorIndex.{u, v})
      d.{u, v} b.{u, v} S.{u, v} L.{u, v}
      (indexFunctor.{u, v}) r X (toModule F) ((RightShift.shift r).obj F) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.rawRightShiftRestrictionIso
    (J := OrthogonalOperatorIndex.{u, v})
    d.{u, v} b.{u, v} S.{u, v} L.{u, v}
    (indexFunctor.{u, v}) r X (toModule F) ((RightShift.shift r).obj F) (bareShiftIso r F)



/-- Every actual enrichment-base parameter is represented by the original full source functions. -/
abbrev parameterEquiv (r : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (N : SourceModule.{u, v}) (c : OrthogonalIndex) (P : PointedCGWH.{u, v}) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c P

/-- Every original parameter retains its complete enriched free-source family. -/
abbrev familyEquiv (r : OrthogonalIndex) (X : PointedCGWH.{u, v})
    (N : SourceModule.{u, v}) (c : OrthogonalIndex) (P : PointedCGWH.{u, v}) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.familyEquiv d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c P

/-- The native forward value is the unchanged original two-unit generator evaluation. -/
theorem value_generator :
    ∀ (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (N : Module d.{u, v} S.{u, v} L.{u, v})
      (c : OrthogonalIndex),
      (ModuleMappingR.FreeEvaluation.valueIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c).hom = π d.{u, v}
        b.{u, v} S.{u, v} L.{u, v} (ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r X) N c r ≫
        (MonoidalClosed.pre
          (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.generatorMap d.{u, v} S.{u, v} L.{u, v} r X)).app
          ((SphereModuleMappingEnd.diagram d.{u, v} S.{u, v} L.{u, v} N).toEnrichedFunctor.obj (r ⊗ c)) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso_generator d.{u, v} b.{u, v} S.{u, v} L.{u, v}

/-- The native inverse retains every original free-I family projection. -/
theorem inverse_restriction :
    ∀ (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (N : Module d.{u, v} S.{u, v} L.{u, v})
      (c j : OrthogonalIndex),
      (ModuleMappingR.FreeEvaluation.valueIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c).inv ≫ π d.{u, v}
        b.{u, v} S.{u, v} L.{u, v} (ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r X) N c j ≫
        (MonoidalClosed.pre (component (freeUnit d.{u, v} S.{u, v} L.{u, v} (Free.object r X)) j)).app
          ((SphereModuleMappingEnd.diagram d.{u, v} S.{u, v} L.{u, v} N).toEnrichedFunctor.obj (j ⊗ c)) =
        FreeWeightedEnd.inverse r X (Closed.translatedTarget d.{u, v} (SphereModuleMappingEnd.diagram d.{u,
          v} S.{u, v} L.{u, v} N) c).toEnrichedFunctor ≫
          Closed.π d.{u, v} (Free.object r X) (SphereModuleMappingEnd.diagram d.{u, v} S.{u, v} L.{u, v} N) c j :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso_inv_restriction d.{u, v} b.{u, v} S.{u, v} L.{u, v}

/-- Every native target arrow retains its literal complete right-translated value. -/
theorem value_target :
    ∀ (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) {N N' : Module d.{u, v} S.{u, v} L.{u, v}}
      (g : N ⟶ N') (c : OrthogonalIndex),
      component (post d.{u, v} b.{u, v} S.{u, v} L.{u, v} (ModuleMappingR.FreeEvaluation.freeAt d.{u, v}
        S.{u, v} L.{u, v} r X) g) c ≫
        (ModuleMappingR.FreeEvaluation.valueIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N' c).hom =
          (ModuleMappingR.FreeEvaluation.valueIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c).hom ≫
          (ihom X).map (component (SphereModuleMappingEnd.moduleMap d.{u, v} S.{u, v} L.{u, v} g) (r ⊗ c)) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso_target d.{u, v} b.{u, v} S.{u, v} L.{u, v}

/-- Every actual free source arrow retains the original full weighted-end transpose. -/
theorem value_sourceMap :
    ∀ (r s : OrthogonalIndex) (X Y : PointedCGWH.{u, v})
      (f : Free.object s Y ⟶ Free.object r X) (N : Module d.{u, v} S.{u, v} L.{u, v}) (c : OrthogonalIndex),
      component (pre d.{u, v} b.{u, v} S.{u, v} L.{u, v} (freeMap d.{u, v} S.{u, v} L.{u, v} f) N) c ≫
        (ModuleMappingR.FreeEvaluation.valueIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} s Y N c).hom =
          (ModuleMappingR.FreeEvaluation.valueIso d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c).hom ≫
          FreeWeightedEndMap.transpose r s X Y
            (Closed.translatedTarget d.{u, v} (SphereModuleMappingEnd.diagram d.{u, v} S.{u, v} L.{u, v} N)
              c).toEnrichedFunctor f :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso_sourceMap d.{u, v} b.{u, v} S.{u, v} L.{u, v}

/-- Every actual stock source arrow uses complete free-generator restriction and evaluation. -/
theorem value_sourceArrow :
    ∀ (r s : OrthogonalIndex) (X Y : PointedCGWH.{u, v})
      (f : ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} s Y ⟶
        ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r X) (N : Module d.{u, v} S.{u, v}
        L.{u, v}) (c : OrthogonalIndex),
      component (pre d.{u, v} b.{u, v} S.{u, v} L.{u, v} f N) c ≫ (ModuleMappingR.FreeEvaluation.valueIso
        d.{u, v} b.{u, v} S.{u, v} L.{u, v} s Y N c).hom =
        valueι d.{u, v} b.{u, v} S.{u, v} L.{u, v} (ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v}
          L.{u, v} r X) N c ≫
          component (Closed.pre d.{u, v}
            (freeUnit d.{u, v} S.{u, v} L.{u, v} (Free.object s Y) ≫
              SphereModuleMappingEnd.moduleMap d.{u, v} S.{u, v} L.{u, v} f)
                (SphereModuleMappingEnd.diagram d.{u, v} S.{u, v} L.{u, v} N)) c ≫
          FreeWeightedEnd.forward s Y (Closed.translatedTarget d.{u, v} (SphereModuleMappingEnd.diagram
            d.{u, v} S.{u, v} L.{u, v} N) c).toEnrichedFunctor :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.valueIso_sourceArrow d.{u, v} b.{u, v} S.{u, v} L.{u, v}

/-- All parameter objects use the original closed evaluation and actual inverse extension. -/
theorem parameter_apply :
    ∀ (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (N : Module d.{u, v} S.{u, v} L.{u, v})
      (c : OrthogonalIndex) {P : PointedCGWH.{u, v}}
      (f : P ⟶ value d.{u, v} b.{u, v} S.{u, v} L.{u, v} (ModuleMappingR.FreeEvaluation.freeAt d.{u, v}
        S.{u, v} L.{u, v} r X) N c),
      ModuleMappingR.FreeEvaluation.parameterEquiv d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c P f =
        MonoidalClosed.uncurry (f ≫ (ModuleMappingR.FreeEvaluation.valueIso d.{u, v} b.{u, v} S.{u, v}
        L.{u, v} r X N c).hom) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv_apply d.{u, v} b.{u, v} S.{u, v} L.{u, v}

/-- Both original inverse maps are retained at every arbitrary parameter object. -/
theorem parameter_symm_apply :
    ∀ (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (N : Module d.{u, v} S.{u, v} L.{u, v})
      (c : OrthogonalIndex) {P : PointedCGWH.{u, v}}
      (q : X ⊗ P ⟶ (SphereModuleMappingEnd.diagram d.{u, v} S.{u, v} L.{u, v} N).toEnrichedFunctor.obj (r ⊗ c)),
      (ModuleMappingR.FreeEvaluation.parameterEquiv d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c P).symm q =
        MonoidalClosed.curry q ≫ (ModuleMappingR.FreeEvaluation.valueIso d.{u, v} b.{u, v} S.{u, v} L.{u,
        v} r X N c).inv :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv_symm_apply d.{u, v} b.{u, v} S.{u, v} L.{u, v}

/-- The full native parameter evaluates on the whole original free-module generator. -/
theorem parameter_generator :
    ∀ (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (N : Module d.{u, v} S.{u, v} L.{u, v})
      (c : OrthogonalIndex) {P : PointedCGWH.{u, v}}
      (f : P ⟶ value d.{u, v} b.{u, v} S.{u, v} L.{u, v} (ModuleMappingR.FreeEvaluation.freeAt d.{u, v}
        S.{u, v} L.{u, v} r X) N c),
      ModuleMappingR.FreeEvaluation.parameterEquiv d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c P f =
        (CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.generatorMap d.{u, v} S.{u, v} L.{u, v} r X ▷ P) ≫
          MonoidalClosed.uncurry (f ≫ π d.{u, v} b.{u, v} S.{u, v} L.{u, v}
            (ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v} L.{u, v} r X) N c r) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv_generator d.{u, v} b.{u, v} S.{u, v} L.{u, v}

/-- Every native parameter arrow retains original coefficient tensoring before evaluation. -/
theorem parameter_regrade :
    ∀ (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (N : Module d.{u, v} S.{u, v} L.{u, v})
      (c : OrthogonalIndex) {P Q : PointedCGWH.{u, v}} (h : P ⟶ Q)
      (f : Q ⟶ value d.{u, v} b.{u, v} S.{u, v} L.{u, v} (ModuleMappingR.FreeEvaluation.freeAt d.{u, v}
        S.{u, v} L.{u, v} r X) N c),
      ModuleMappingR.FreeEvaluation.parameterEquiv d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c P (h ≫ f) =
        (X ◁ h) ≫ ModuleMappingR.FreeEvaluation.parameterEquiv d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c Q f :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.parameterEquiv_regrade d.{u, v} b.{u, v} S.{u, v} L.{u, v}

/-- The full native parameter family retains each complete source-index component. -/
theorem family_app :
    ∀ (r : OrthogonalIndex) (X : PointedCGWH.{u, v}) (N : Module d.{u, v} S.{u, v} L.{u, v})
      (c : OrthogonalIndex) {P : PointedCGWH.{u, v}}
      (f : P ⟶ value d.{u, v} b.{u, v} S.{u, v} L.{u, v} (ModuleMappingR.FreeEvaluation.freeAt d.{u, v}
        S.{u, v} L.{u, v} r X) N c) (j : OrthogonalIndex),
      (ModuleMappingR.FreeEvaluation.familyEquiv d.{u, v} b.{u, v} S.{u, v} L.{u, v} r X N c P f).app j =
        f ≫ π d.{u, v} b.{u, v} S.{u, v} L.{u, v} (ModuleMappingR.FreeEvaluation.freeAt d.{u, v} S.{u, v}
          L.{u, v} r X) N c j ≫
          (MonoidalClosed.pre (component (freeUnit d.{u, v} S.{u, v} L.{u, v} (Free.object r X)) j)).app
            ((SphereModuleMappingEnd.diagram d.{u, v} S.{u, v} L.{u, v} N).toEnrichedFunctor.obj (j ⊗ c)) :=
  CategoryTheory.Enriched.ModuleMappingR.FreeEvaluation.familyEquiv_app d.{u, v} b.{u, v} S.{u, v} L.{u, v}

end PointedCGWH.Spectra.Orthogonal.FunctionSpectrum.FreeSource
