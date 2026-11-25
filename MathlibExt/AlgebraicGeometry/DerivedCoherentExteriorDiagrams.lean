/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedUniversalAffineSplittingMaps
public import MathlibExt.AlgebraicGeometry.DerivedNativeFormComparisons
public import MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
public import MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
public import MathlibExt.AlgebraicGeometry.DerivedResolvedExteriorDiagrams

/-!
# Coherent exterior diagrams from the full universal affine differential

Each affine differential is the entire coefficient-natural cotangent
transpose of the literal universal evaluation Spec(A) times Map(Spec(A),F)
to F. Its source is the actual based derivation functor. The exterior
arrow is computed by native inclusion, tensor(df,df), and projection.

Coefficient extraction evaluates the enriched source functor on the
actual coefficient unit. Source affine comparisons retain the scalar
shuffle, balanced quotient, both skew-image maps and original QA form
generators. The map is a full DG coefficient-section map on a projective
source resolution. The actual RΓ cone first enters the injective exterior
coefficient diagram. Only after localization of entire diagrams is that
source augmentation inverted and the exterior map applied. The final
cone enters the injective weight replacement and is normalized by its
entire localized diagram class. Constructing this data is Wanted work.

Sources: PTVV arXiv:1111.3209v4, Section 1.2, Proposition 1.14 and
Lemma 1.15; HAG II arXiv:math/0404373v7, Sections 1.3.7 and 1.4.1.
Native DG, balanced tensor, Dold--Kan and public-source notices remain
in the imported modules. Provider theory is not an entry requirement.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCoherentExteriorDiagrams

open _root_.CategoryTheory _root_.CategoryTheory.Limits
open _root_.CategoryTheory.MonoidalCategory _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedAlongDerivations
open MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
open MathlibExt.AlgebraicGeometry.DerivedGlobalCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
open MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedUniversalAffineSplittingMaps
open MathlibExt.AlgebraicGeometry.DerivedNativeFormComparisons
open MathlibExt.AlgebraicGeometry.DerivedResolvedExteriorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open CochainComplex.HomComplex
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]
variable {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {R : RawModuleRealization M} {X Y : Prestack k}
    {GX : QCohEnhancement M U X} {GY : QCohEnhancement M U Y}

/-- A source differential retains both native representing comparisons and every full coefficient map.
Its differential is relative to the chosen along representation, so it is determined only up to the
automorphisms of `f^* L_Y` (see `CotangentDifferential`). -/
structure CotangentAlongSource (CY : CotangentContext R GY) (f : X ⟶ Y)
    (PB : PullbackDGModel f GY GX) where
  context : CotangentContext R GX
  projection : AlongLiftProjection M R context.kernels f context.projection
  path : AlongPath M R context.kernels Y
  pathMap : AlongPathMap M R context.kernels f context.path path
  raw : AlongRawMap M R context.kernels f context.projection projection context.path path pathMap
  derivations : AlongDerivationModel M R context.kernels f context.projection projection path
  replacement : AlongReplacementMap M R context.kernels raw context.derivations derivations
  fibration : AlongFibration M R context.kernels derivations
  fibrationMap : AlongFibrationMap M R context.kernels replacement context.fibration fibration
  representation : AlongCotangentRepresentation context f projection path derivations fibration
    (PB.functor.obj CY.cotangent.object)
  differential : CotangentDifferential context CY f PB replacement fibration fibrationMap representation

/-- Pullback tensor comparison is one full native parameter homotopy, not separate object isomorphisms. -/
structure TensorPullbackSource (HY : CoherentMonoidalEnhancement GY)
    (HX : CoherentMonoidalEnhancement GX) {f : X ⟶ Y} (PB : PullbackDGModel f GY GX) where
  map : ∀ E F : GY.category,
    DGHom (LargeScalar k) 0 (PB.functor.obj (HY.monoidal.tensor.obj (E, F)))
      (HX.monoidal.tensor.obj (PB.functor.obj E, PB.functor.obj F))
  closed : ∀ E F : GY.category, map E F ∈ dgCycles (LargeScalar k) _ _
  homotopy : (dgNerve (k := LargeScalar k) GY.category ⊗
    dgNerve (k := LargeScalar k) GY.category) ⊗ (Δ[1] : SSet.{u + 1}) ⟶
      dgNerve (k := LargeScalar k) GX.category
  first : parameterAt _ 0 ≫ homotopy = HY.monoidal.nerve.map ≫ dgNerveMap PB.functor
  second : parameterAt _ 1 ≫ homotopy =
    (dgNerveMap PB.functor ⊗ₘ dgNerveMap PB.functor) ≫ HX.monoidal.nerve.map
  coefficients : ∀ E F : GY.category,
    homotopy.app (op ⦋1⦌)
      (((dgNerve (k := LargeScalar k) GY.category).σ 0 (objectVertex E),
        (dgNerve (k := LargeScalar k) GY.category).σ 0 (objectVertex F)),
        SSet.stdSimplex.edge 1 0 1 (by decide)) = (dgEdge (map E F) (closed E F)).edge

/-- The pullback exterior image is computed from the original inclusion and actual tensor comparison. -/
def pullbackExterior [Algebra ℚ k] (HY : CoherentMonoidalEnhancement GY)
    (HX : CoherentMonoidalEnhancement GX) {f : X ⟶ Y} (PB : PullbackDGModel f GY GX)
    (B : TensorPullbackSource HY HX PB) {L : GY.category} (E : ExteriorSquare HY L)
    (E' : ExteriorSquare HX (PB.functor.obj L)) :
    DGHom (LargeScalar k) 0 (PB.functor.obj E.object) E'.object :=
  dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
    (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
      (PB.functor.dgMap 0 E.inclusion) (B.map L L) (by omega)) E'.projection (by omega)

/-- The actual pullback exterior composite is closed. -/
theorem pullbackExterior_closed [Algebra ℚ k] (HY : CoherentMonoidalEnhancement GY)
    (HX : CoherentMonoidalEnhancement GX) {f : X ⟶ Y} (PB : PullbackDGModel f GY GX)
    (B : TensorPullbackSource HY HX PB) {L : GY.category} (E : ExteriorSquare HY L)
    (E' : ExteriorSquare HX (PB.functor.obj L)) :
    pullbackExterior HY HX PB B E E' ∈ dgCycles (LargeScalar k) _ _ := by
  rw [mem_dgCycles, pullbackExterior, dgDifferential_dgComp, dgDifferential_dgComp,
    (mem_dgCycles (LargeScalar k)).mp E'.projection_closed,
    (mem_dgCycles (LargeScalar k)).mp (B.closed L L), ← PB.functor.dgMap_dgDifferential,
    (mem_dgCycles (LargeScalar k)).mp E.inclusion_closed, map_zero]
  simp

/-- An actual closed global map is evaluated by the full native coefficient DG functor. -/
def coefficientClosedMap {L : CochainLiftModel k} (C : GammaCechData L GX)
    (j : Families X) {E F : GX.category} (d : DGHom (LargeScalar k) 0 E F)
    (hd : d ∈ dgCycles (LargeScalar k) E F) :
    (C.source.diagram.obj j).toEnrichedFunctor.obj E ⟶
      (C.source.diagram.obj j).toEnrichedFunctor.obj F := by
  let z := (C.source.diagram.obj j).toEnrichedFunctor.dgMap 0 d
  have hz : dgDifferential (LargeScalar k) 0 z = 0 := by
    rw [← (C.source.diagram.obj j).toEnrichedFunctor.dgMap_dgDifferential,
      (mem_dgCycles (LargeScalar k)).mp hd, map_zero]
  exact Cocycle.homOf (Cocycle.mk z 1 rfl (by
    simpa only [dgDifferential_linearHomComplex, zero_add] using! hz))

/-- The coefficient unit is fixed by the actual affine regular unit augmentation. -/
structure CoefficientSourceUnit {L : CochainLiftModel k} (C : GammaCechData L GX)
    (j : Families X) where
  map : 𝟙_ (Cochains (LargeScalar k)) ⟶ (C.source.diagram.obj j).toEnrichedFunctor.obj GX.unit
  normalized : map ≫ C.unit.augmentation.app j ≫ eqToHom (C.unit.value j) =
    affineCoefficientUnit L N ((algebraProjection X).obj j)
  evaluation : ∀ E : GX.category,
    UnitEvaluationModel ((C.source.diagram.obj j).toEnrichedFunctor.obj E)

/-- RΓ coefficient extraction is native enriched evaluation on that same actual unit. -/
def coefficientRestriction {L : CochainLiftModel k} (C : GammaCechData L GX)
    (j : Families X) (V : CoefficientSourceUnit C j) (E : GX.category) :
    globalHom GX E ⟶ (C.source.diagram.obj j).toEnrichedFunctor.obj E :=
  (C.source.diagram.obj j).toEnrichedFunctor.map GX.unit E ≫
    linearHomComplexPrecomp (LargeScalar k) V.map
      ((C.source.diagram.obj j).toEnrichedFunctor.obj E) ≫ (V.evaluation E).comparison.hom

variable [Algebra ℚ k]

/-- Native affine exterior coefficients retain both skew-image maps and the complete QA action. -/
structure AffineExteriorCoefficients {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (A : SAlg k) {L : CochainLiftModel k} (C : GammaCechData L GX)
    (H : CoherentMonoidalEnhancement GX) (LC : GX.category) (EX : ExteriorSquare H LC)
    (j : Families X) (hA : (algebraProjection X).obj j = Q.functor.obj A) where
  cotangent : ResolvedCotangentModule N D A
  tensor : DerivedTensorModel (coefficientCategory N (Q.functor.obj A)) PUnit.unit
  unit : DGDerivedModules k (coefficientCategory N (Q.functor.obj A))
  unit_eq : unit.obj = regularModule (coefficientCategory N (Q.functor.obj A)) PUnit.unit
  coherence : CoherenceModel (coefficientCategory N (Q.functor.obj A)) PUnit.unit tensor unit unit_eq
  exterior : ModuleExteriorSquare (coefficientCategory N (Q.functor.obj A)) PUnit.unit
    tensor unit unit_eq coherence cotangent.module
  wedge : NormalizedFormWedge (D.forms A)
  forms : ResolvedExteriorFormComparison N D A cotangent tensor unit unit_eq coherence exterior wedge
  cotangentValue : (C.source.diagram.obj j).toEnrichedFunctor.obj LC ≅
    (largeCochainLift k).obj (DerivedCoefficientTensorModels.value
      (coefficientCategory N (Q.functor.obj A)) PUnit.unit cotangent.module.obj)
  tensorValue : (C.source.diagram.obj j).toEnrichedFunctor.obj (H.monoidal.tensor.obj (LC, LC)) ≅
    (largeCochainLift k).obj (DerivedCoefficientTensorModels.value
      (coefficientCategory N (Q.functor.obj A)) PUnit.unit (tensor.functor.obj
        (cotangent.module, cotangent.module)).obj)
  map : (C.source.diagram.obj j).toEnrichedFunctor.obj EX.object ⟶
    (largeCochainLift k).obj (DerivedCoefficientTensorModels.value
      (coefficientCategory N (Q.functor.obj A)) PUnit.unit exterior.module.obj)
  inclusion : map ≫ (largeCochainLift k).map
    (moduleComponent ((DGFunctor.homEquivDGCycles k _ _).symm
      ⟨exterior.inclusion, exterior.inclusion_closed⟩) (op PUnit.unit)) =
    coefficientClosedMap C j EX.inclusion EX.inclusion_closed ≫ tensorValue.hom
  projection : coefficientClosedMap C j EX.projection EX.projection_closed ≫ map =
    tensorValue.hom ≫ (largeCochainLift k).map
      (moduleComponent ((DGFunctor.homEquivDGCycles k _ _).symm
        ⟨exterior.projection, exterior.projection_closed⟩) (op PUnit.unit))
  scalarAction : letI := C.category.enrichment
    ∀ (p q r : ℤ) (h : q + p = r)
    (a : (N.functor.obj (Q.functor.obj A)).X.X p)
    (m : ((C.source.diagram.obj j).toEnrichedFunctor.obj LC).X q),
    ((cotangentValue.hom.f r).hom
      ((eqToHom (C.source.value LC j).symm).f r
        (((C.source.sections.obj LC).toEnrichedFunctor.dgMap p
          (generator C.category (𝟙 j) p
            ((affineCoefficientMap L N (eqToHom hA.symm)).f p (ULift.up a))) :
            Cochain _ _ p).v q r h
          (((eqToHom (C.source.value LC j)).f q).hom m)))) =
      ULift.up (DerivedCotangentModels.moduleAction cotangent.module.obj (op PUnit.unit)
        a h (((cotangentValue.hom.f q).hom m).down))

/-- The affine form coefficient is the same exterior coefficient map followed by the native normalized wedge comparison. -/
def affineExteriorFormMap {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {A : SAlg k} {L : CochainLiftModel k} {C : GammaCechData L GX}
    {H : CoherentMonoidalEnhancement GX} {LC : GX.category} {EX : ExteriorSquare H LC}
    {j : Families X} {hA : (algebraProjection X).obj j = Q.functor.obj A}
    (B : AffineExteriorCoefficients D A C H LC EX j hA) :
    (C.source.diagram.obj j).toEnrichedFunctor.obj EX.object ⟶
      ((globalToCoefficients k).obj ((liftComplex k).obj ((D.functor.obj A).weight 2)))⟦-2⟧ :=
  B.map ≫ (largeCochainLift k).map B.forms.map ≫ affineCoefficientFormMap D A

/-- Coupled native models of the full universal affine differential and its source form coefficients. -/
structure UniversalExteriorFamilies {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (L : CochainLiftModel k) (F : Prestack k) (G : QCohEnhancement M U F)
    (CY : CotangentContext R G) (H : CoherentMonoidalEnhancement G)
    (E : ExteriorSquare H CY.cotangent.object) where
  model : ∀ A : SAlg k, QCohEnhancement M U (universalDomain Q F A)
  pullback : ∀ A : SAlg k, PullbackDGModel (universalEvaluation Q F A) G (model A)
  unit : ∀ A : SAlg k, (pullback A).functor.obj G.unit = (model A).unit
  differential : ∀ A : SAlg k, CotangentAlongSource CY (universalEvaluation Q F A) (pullback A)
  monoidal : ∀ A : SAlg k, CoherentMonoidalEnhancement (model A)
  tensor : ∀ A : SAlg k, TensorPullbackSource H (monoidal A) (pullback A)
  pulledExterior : ∀ A : SAlg k,
    ExteriorSquare (monoidal A) ((pullback A).functor.obj CY.cotangent.object)
  affineExterior : ∀ A : SAlg k,
    ExteriorSquare (monoidal A) (differential A).context.cotangent.object
  coefficients : ∀ A : SAlg k, GammaCechData L (model A)
  coefficientUnit : ∀ j : Families (affineParameterPrestack Q F),
    CoefficientSourceUnit (coefficients j.obj.1) (resolvedParameterFamily Q F j)
  forms : ∀ j : Families (affineParameterPrestack Q F),
    AffineExteriorCoefficients D j.obj.1 (coefficients j.obj.1) (monoidal j.obj.1)
      (differential j.obj.1).context.cotangent.object (affineExterior j.obj.1)
      (resolvedParameterFamily Q F j) rfl

/-- Literal RΓ pullback uses the actual enriched functor and its actual structure unit. -/
def universalSectionPullback {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E)
    (A : SAlg k) : globalHom G E.object ⟶
      globalHom (B.model A) ((B.pullback A).functor.obj E.object) :=
  (B.pullback A).functor.map G.unit E.object ≫
    eqToHom (by rw [B.unit A]; rfl)

/-- The whole chart exterior arrow is the computed pullback image followed by exterior(df). -/
def universalExteriorArrow {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E)
    (A : SAlg k) : DGHom (LargeScalar k) 0 ((B.pullback A).functor.obj E.object)
      (B.affineExterior A).object :=
  dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
    (pullbackExterior H (B.monoidal A) (B.pullback A) (B.tensor A) E (B.pulledExterior A))
    (exteriorDifferential (B.monoidal A) (B.differential A).differential.map
      (B.pulledExterior A) (B.affineExterior A)) (by omega)

/-- Both native exterior composites prove closure of that same chart arrow. -/
theorem universalExteriorArrow_closed {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E)
    (A : SAlg k) : universalExteriorArrow B A ∈ dgCycles (LargeScalar k) _ _ := by
  rw [mem_dgCycles, universalExteriorArrow, dgDifferential_dgComp,
    (mem_dgCycles (LargeScalar k)).mp
      (pullbackExterior_closed H (B.monoidal A) (B.pullback A) (B.tensor A) E (B.pulledExterior A)),
    (mem_dgCycles (LargeScalar k)).mp
      (exteriorDifferential_closed (B.monoidal A) (B.differential A).differential.map
        (B.differential A).differential.closed (B.pulledExterior A) (B.affineExterior A))]
  simp

/-- The actual chart map uses pullback, exterior(df), coefficient unit, polynomial shuffle and native weight shift. -/
def chartExteriorFormMap {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E)
    (j : Families (affineParameterPrestack Q F)) : globalHom G E.object ⟶
      ((globalToCoefficients k).obj ((liftComplex k).obj ((D.functor.obj j.obj.1).weight 2)))⟦-2⟧ :=
  universalSectionPullback B j.obj.1 ≫
    eHomWhiskerLeft (Cochains (LargeScalar k))
      (ForgetEnrichment.of _ (B.model j.obj.1).unit)
      (dgClosedHomOf (LargeScalar k) (universalExteriorArrow B j.obj.1)
        (universalExteriorArrow_closed B j.obj.1)) ≫
    coefficientRestriction (B.coefficients j.obj.1) (resolvedParameterFamily Q F j)
      (B.coefficientUnit j) (B.affineExterior j.obj.1).object ≫
    affineExteriorFormMap (B.forms j)

/-- The source unshifted exterior convention is actual DR weight two followed by shift minus two. -/
def coefficientWeightFunctor (k : Type u) [CommRing k] :
    GlobalComplex k ⥤ Cochains (LargeScalar k) :=
  globalToCoefficients k ⋙ shiftFunctor (Cochains (LargeScalar k)) (-2 : ℤ)

/-- The whole actual affine mapping/simplex de Rham weight diagram. -/
def parameterWeightDiagram {Q : AlgebraReplacementFunctor k} (D : AffineDRSystem Q)
    (F : Prestack k) :=
  weightDiagram D 2 (affineParameterPrestack Q F) ⋙ coefficientWeightFunctor k

/-- The native all-E coefficient functor uses the whole actual universal evaluation pullback. -/
def universalCoefficientFunctor {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E)
    (j : Families (affineParameterPrestack Q F)) :
    DGFunctor (LargeScalar k) G.category (Cochains (LargeScalar k)) :=
  ⟨(B.pullback j.obj.1).functor.comp (Cochains (LargeScalar k))
    ((B.coefficients j.obj.1).source.diagram.obj (resolvedParameterFamily Q F j)).toEnrichedFunctor⟩

/-- The entire native universal injective coefficient functor is assembled before any raw form target. -/
def universalInjectiveCoefficientFunctor {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E)
    (j : Families (affineParameterPrestack Q F)) :
    DGFunctor (LargeScalar k) G.category (Cochains (LargeScalar k)) :=
  ⟨(B.pullback j.obj.1).functor.comp (Cochains (LargeScalar k))
    ((B.coefficients j.obj.1).replacement.diagram.obj (resolvedParameterFamily Q F j)).toEnrichedFunctor⟩

/-- Every source cochain first uses actual Γ pullback, then the actual universal GammaCechData map
and its native injective limit projection. It never enters raw QA forms at this stage. -/
def universalGlobalSectionProjection {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E)
    (V : G.category) (j : Families (affineParameterPrestack Q F)) :
    globalHom G V ⟶ (universalInjectiveCoefficientFunctor B j).toEnrichedFunctor.obj V :=
  (B.pullback j.obj.1).functor.map G.unit V ≫
    eqToHom (by rw [B.unit j.obj.1]; rfl) ≫
    globalSectionMap (B.coefficients j.obj.1).category (B.model j.obj.1)
      (B.coefficients j.obj.1).comparison ((B.pullback j.obj.1).functor.obj V) ≫
    limit.π (evaluateDiagram (B.coefficients j.obj.1).replacement.diagram
      ((B.pullback j.obj.1).functor.obj V)) (resolvedParameterFamily Q F j)

/-- This map acts on exterior coefficients, before any global RΓ cone is taken. -/
def universalExteriorCoefficientMap {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E)
    (j : Families (affineParameterPrestack Q F)) :
    (universalCoefficientFunctor B j).toEnrichedFunctor.obj E.object ⟶
      (parameterWeightDiagram D F).obj j :=
  coefficientClosedMap (B.coefficients j.obj.1) (resolvedParameterFamily Q F j)
    (universalExteriorArrow B j.obj.1) (universalExteriorArrow_closed B j.obj.1) ≫
      affineExteriorFormMap (B.forms j)

/-- The source retains all-E DG section maps, all homogeneous coefficient
actions and the literal native cotangent transpose. Its exterior map
has a projective source and an actual derived-scalar target. -/
structure ExteriorCoefficientSources {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E) where
  cech : GammaCechData L G
  sourceModel : SourceEnrichedQCohModel cech.category G R cech.source cech.unit
  polynomial : PolynomialAlgebraDiagram Q (affineParameterPrestack Q F)
  span : PolynomialExteriorSpan (N := N) D polynomial
  coefficients : AlgebraDiagramCoefficientCategory L N polynomial.algebra
  diagrams : AlgebraSectionDiagrams coefficients
  source : letI := coefficients.enrichment
    DGFunctor (LargeScalar k) G.category (AlgebraCoefficientSection coefficients)
  sourceDiagram : Families (affineParameterPrestack Q F) ⥤
    DGFunctor (LargeScalar k) G.category (Cochains (LargeScalar k))
  sourceValue : letI := coefficients.enrichment
    ∀ (V : G.category) (j : Families (affineParameterPrestack Q F)),
    (sourceDiagram.obj j).toEnrichedFunctor.obj V =
      (source.toEnrichedFunctor.obj V).toEnrichedFunctor.obj j
  sourceHomogeneous : letI := coefficients.enrichment
    ∀ (V W : G.category) (p : ℤ) (f : DGHom (LargeScalar k) p V W)
      (j : Families (affineParameterPrestack Q F)),
    HEq ((sourceDiagram.obj j).toEnrichedFunctor.dgMap p f)
      (DGFunctor.dgApp (LargeScalar k) p j (source.toEnrichedFunctor.dgMap p f))
  sourceDiagram_eq : letI := coefficients.enrichment
    ∀ V : G.category, diagrams.functor.obj (source.toEnrichedFunctor.obj V) =
      evaluateDiagram sourceDiagram V
  sourceCofibrant : letI := coefficients.enrichment
    ∀ V : G.category, ∀ (A C : AlgebraCoefficientSection coefficients) (p : A ⟶ C),
      (∀ j, QuasiIso (evaluationMap p j) ∧
        ∀ n : ℤ, Function.Surjective ((evaluationMap p j).f n)) →
      ∀ f : source.toEnrichedFunctor.obj V ⟶ C,
        ∃ g : source.toEnrichedFunctor.obj V ⟶ A, g ≫ p = f
  sourceAugmentation : sourceDiagram ⟶
    reindex (affineParameterPoint Q F) ⋙ cech.source.diagram
  sourceWeak : ∀ (V : G.category) (j : Families (affineParameterPrestack Q F)),
    QuasiIso ((evaluateDiagramMap sourceAugmentation V).app j)
  sourceAction : letI := coefficients.enrichment
    letI := cech.category.enrichment
    ∀ (V : G.category) (j l : Families (affineParameterPrestack Q F)) (f : j ⟶ l)
      (p q r : ℤ) (h : q + p = r)
      (a : (affineCoefficient L N (polynomial.algebra.obj l)).X p)
      (m : ((sourceDiagram.obj j).toEnrichedFunctor.obj V).X q),
    (((evaluateDiagramMap sourceAugmentation V).app l).f r).hom
      (((eqToHom (sourceValue V l).symm).f r).hom
        (((source.toEnrichedFunctor.obj V).toEnrichedFunctor.dgMap p
          (algebraGenerator coefficients f p a) : Cochain _ _ p).v q r h
          (((eqToHom (sourceValue V j)).f q).hom m))) =
      ((eqToHom (cech.source.value V ((reindex (affineParameterPoint Q F)).obj l)).symm).f r).hom
        (((cech.source.sections.obj V).toEnrichedFunctor.dgMap p
          (generator cech.category ((reindex (affineParameterPoint Q F)).map f) p
            (((affineCoefficientMap L N (polynomial.augmentation.app l)).f p).hom a)) :
              Cochain _ _ p).v q r h
          (((eqToHom (cech.source.value V ((reindex (affineParameterPoint Q F)).obj j))).f q).hom
            (((evaluateDiagramMap sourceAugmentation V).app j).f q m)))
  universalDiagram : Families (affineParameterPrestack Q F) ⥤
    DGFunctor (LargeScalar k) G.category (Cochains (LargeScalar k))
  universalObject : ∀ j, universalDiagram.obj j = universalCoefficientFunctor B j
  nativePullback : sourceDiagram ⟶ universalDiagram
  universalSource : ∀ A : SAlg k,
    SourceEnrichedQCohModel (B.coefficients A).category (B.model A) R
      (B.coefficients A).source (B.coefficients A).unit
  universalInjectiveDiagram : Families (affineParameterPrestack Q F) ⥤
    DGFunctor (LargeScalar k) G.category (Cochains (LargeScalar k))
  universalInjectiveObject : ∀ j,
    universalInjectiveDiagram.obj j = universalInjectiveCoefficientFunctor B j
  universalAugmentation : universalDiagram ⟶ universalInjectiveDiagram
  universalAugmentation_normalized : ∀ (V : G.category) j,
    evaluationMap (universalAugmentation.app j) V =
      eqToHom (congrArg (fun T => T.toEnrichedFunctor.obj V) (universalObject j)) ≫
      evaluationMap ((B.coefficients j.obj.1).replacement.augmentation.app
        (resolvedParameterFamily Q F j)) ((B.pullback j.obj.1).functor.obj V) ≫
      eqToHom (congrArg (fun T => T.toEnrichedFunctor.obj V) (universalInjectiveObject j)).symm
  universalGlobalSectionCone : ∀ V : G.category,
    (Functor.const (Families (affineParameterPrestack Q F))).obj (globalHom G V) ⟶
      evaluateDiagram universalInjectiveDiagram V
  universalGlobalSectionCone_normalized : ∀ (V : G.category) j,
    (universalGlobalSectionCone V).app j = universalGlobalSectionProjection B V j ≫
      eqToHom (congrArg (fun T => T.toEnrichedFunctor.obj V) (universalInjectiveObject j)).symm
  universalGlobalSectionHomogeneous : ∀ (V W : G.category) (p : ℤ)
    (f : DGHom (LargeScalar k) p V W) (i : ℤ) j,
    (dgPostcomp (LargeScalar k) (op G.unit) p f : Cochain _ _ p).v i (i + p) rfl ≫
      ((universalGlobalSectionCone W).app j).f (i + p) =
    ((universalGlobalSectionCone V).app j).f i ≫
      ((universalInjectiveDiagram.obj j).toEnrichedFunctor.dgMap p f : Cochain _ _ p).v i (i + p) rfl
  qaUnitDiagram : Families (affineParameterPrestack Q F) ⥤ Cochains (LargeScalar k)
  qaUnitValue : ∀ j, qaUnitDiagram.obj j = affineCoefficient L N (Q.functor.obj j.obj.1)
  qaUnitArrow : ∀ {j l : Families (affineParameterPrestack Q F)} (f : j ⟶ l),
    HEq (qaUnitDiagram.map f) (affineCoefficientMap L N (Q.functor.map f.hom.1))
  universalUnitComparison : evaluateDiagram universalDiagram G.unit ⟶ qaUnitDiagram
  universalUnitComparison_normalized : ∀ j,
    universalUnitComparison.app j =
      eqToHom (congrArg (fun T => T.toEnrichedFunctor.obj G.unit) (universalObject j)) ≫
      eqToHom (congrArg
        (fun V => ((B.coefficients j.obj.1).source.diagram.obj
          (resolvedParameterFamily Q F j)).toEnrichedFunctor.obj V) (B.unit j.obj.1)) ≫
      (B.coefficients j.obj.1).unit.augmentation.app (resolvedParameterFamily Q F j) ≫
      eqToHom ((B.coefficients j.obj.1).unit.value (resolvedParameterFamily Q F j)) ≫
      eqToHom (qaUnitValue j).symm
  qaUnitAugmentation : qaUnitDiagram ⟶
    reindex (affineParameterPoint Q F) ⋙ cech.unit.coefficients
  qaUnitAugmentation_normalized : ∀ j,
    qaUnitAugmentation.app j = eqToHom (qaUnitValue j) ≫
      affineCoefficientMap L N (Q.augmentation.app j.obj.1) ≫
      eqToHom (cech.unit.value ((reindex (affineParameterPoint Q F)).obj j)).symm
  nativePullbackUnit :
    (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).map
      (evaluateDiagramMap nativePullback G.unit ≫ universalUnitComparison ≫ qaUnitAugmentation) =
    (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).map
      (evaluateDiagramMap sourceAugmentation G.unit ≫
        Functor.whiskerLeft (reindex (affineParameterPoint Q F)) cech.unit.augmentation)
  scalarSection : AlgebraCoefficientSection coefficients
  scalarRepresentation : diagrams.functor.obj scalarSection ≅ rawCoefficientDiagram span.scalarFamily
  scalarAction : letI := coefficients.enrichment
    ∀ (j l : Families (affineParameterPrestack Q F)) (f : j ⟶ l)
      (p q r : ℤ) (h : q + p = r)
      (a : (N.functor.obj (polynomial.algebra.obj l)).X.X p)
      (m : (scalarSection.toEnrichedFunctor.obj j).X q),
    HEq
      (((scalarRepresentation.hom.app l).f r).hom
        (((eqToHom (diagrams.value scalarSection l).symm).f r).hom
          ((scalarSection.toEnrichedFunctor.dgMap p
            (algebraGenerator coefficients f p (ULift.up a)) : Cochain _ _ p).v q r h m)))
      (ULift.up.{u + 1} (DerivedCotangentModels.moduleAction (span.scalarFamily.obj l).module (op PUnit.unit)
        (((N.functor.map (polynomial.augmentation.app l ≫
          eqToHom (congrArg (fun T => T.obj l) span.scalarBase).symm)).hom.f p).hom a) h
        (((span.scalarFamily.map f).map.f q).hom
          ((((scalarRepresentation.hom.app j).f q).hom
            (((eqToHom (diagrams.value scalarSection j).symm).f q).hom m)).down))))
  exterior : letI := coefficients.enrichment
    source.toEnrichedFunctor.obj E.object ⟶ scalarSection
  nativeToQA : evaluateDiagram sourceDiagram E.object ⟶ parameterWeightDiagram D F
  nativeToQA_normalized : ∀ j,
    nativeToQA.app j = evaluationMap (nativePullback.app j) E.object ≫
      eqToHom (congrArg (fun T => T.toEnrichedFunctor.obj E.object) (universalObject j)) ≫
        universalExteriorCoefficientMap B j

omit [Algebra ℚ k] in
/-- Objectwise quasi-isomorphisms are inverted in the localization of whole diagrams. -/
theorem diagramMap_isIso {J : Type (u + 1)} [Category.{u} J]
    {A C : J ⥤ Cochains (LargeScalar k)} (f : A ⟶ C) (hf : ∀ j, QuasiIso (f.app j)) :
    IsIso ((diagramQ (LargeScalar k) J).map f) :=
  (diagramWeakEquivalences (LargeScalar k) J).Q_inverts f hf

/-- The all-E source Γ cone uses the actual native full injective coefficient limit. -/
def injectiveGlobalCoefficientCone {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} {B : UniversalExteriorFamilies D L F G CY H E}
    (S : ExteriorCoefficientSources B) (V : G.category) :
    (Functor.const (Families (affineParameterPrestack Q F))).obj (globalHom G V) ⟶
      reindex (affineParameterPoint Q F) ⋙ evaluateDiagram S.cech.replacement.diagram V :=
  Functor.whiskerLeft (reindex (affineParameterPoint Q F))
    ((limit.cone (evaluateDiagram S.cech.replacement.diagram V)).extend
      (globalSectionMap S.cech.category G S.cech.comparison V)).π

/-- The all-E localized coefficient class applies actual source augmentation inverses,
the full native pullback and the ACTUAL universal enriched injective augmentation. -/
def globalCoefficientClass {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} {B : UniversalExteriorFamilies D L F G CY H E}
    (S : ExteriorCoefficientSources B) (V : G.category) :
    (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).obj
      ((Functor.const (Families (affineParameterPrestack Q F))).obj (globalHom G V)) ⟶
    (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).obj
      (evaluateDiagram S.universalInjectiveDiagram V) := by
  let q := diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))
  let a := Functor.whiskerLeft (reindex (affineParameterPoint Q F))
    (evaluateDiagramMap S.cech.replacement.augmentation V)
  let b := evaluateDiagramMap S.sourceAugmentation V
  letI := diagramMap_isIso a (fun j => S.cech.replacement.weak V
    ((reindex (affineParameterPoint Q F)).obj j))
  letI := diagramMap_isIso b (S.sourceWeak V)
  exact q.map (injectiveGlobalCoefficientCone S V) ≫ inv (q.map a) ≫ inv (q.map b) ≫
    q.map (evaluateDiagramMap S.nativePullback V) ≫ q.map (evaluateDiagramMap S.universalAugmentation V)

/-- The scalar-normalized exterior arrow is an actual full DG section map. -/
def exteriorScalarDiagramMap {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} {B : UniversalExteriorFamilies D L F G CY H E}
    (S : ExteriorCoefficientSources B) : evaluateDiagram S.sourceDiagram E.object ⟶
      rawCoefficientDiagram S.span.scalarFamily := by
  letI := S.coefficients.enrichment
  exact eqToHom (S.sourceDiagram_eq E.object).symm ≫
    S.diagrams.functor.map S.exterior ≫ S.scalarRepresentation.hom

/-- The entire localized scalar span agrees with the entire native universal
exterior(df) map. These are source comparisons, not an eta equivalence input. -/
structure FullExteriorNormalization {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} {B : UniversalExteriorFamilies D L F G CY H E}
    (S : ExteriorCoefficientSources B) where
  allEGlobalSections : ∀ V : G.category,
    globalCoefficientClass S V =
      (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).map (S.universalGlobalSectionCone V)
  scalarUnitWeak : ∀ j, QuasiIso (S.span.scalarUnit.app j)
  polynomialWeak : ∀ j, QuasiIso ((polynomialToQA S.span).app j)
  normalized : letI := diagramMap_isIso S.span.scalarUnit scalarUnitWeak
    (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).map
      (exteriorScalarDiagramMap S) ≫
      inv ((diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).map S.span.scalarUnit) ≫
      (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).map (polynomialToQA S.span) =
    (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).map S.nativeToQA

/-- The native RΓ cone enters the whole injective exterior coefficient diagram first. -/
def injectiveExteriorCoefficientCone {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} {B : UniversalExteriorFamilies D L F G CY H E}
    (S : ExteriorCoefficientSources B) :
    (Functor.const (Families (affineParameterPrestack Q F))).obj (globalHom G E.object) ⟶
      reindex (affineParameterPoint Q F) ⋙ evaluateDiagram S.cech.replacement.diagram E.object :=
  injectiveGlobalCoefficientCone S E.object

/-- The class uses the actual coefficient augmentation inverse, source resolution,
full DG exterior(df), original scalar/polynomial span and actual target augmentation. -/
def exteriorInjectiveDiagramClass {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} {B : UniversalExteriorFamilies D L F G CY H E}
    (S : ExteriorCoefficientSources B) (T : FullExteriorNormalization S)
    {NC : NegativeCyclicDiagram D.functor (2 : ℤ)}
    (P : GlobalNCModel D 2 NC (affineParameterPrestack Q F)) :
    (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).obj
      ((Functor.const (Families (affineParameterPrestack Q F))).obj (globalHom G E.object)) ⟶
    (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).obj
      (P.ordinary.diagram ⋙ coefficientWeightFunctor k) := by
  let q := diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))
  let a := Functor.whiskerLeft (reindex (affineParameterPoint Q F))
    (evaluateDiagramMap S.cech.replacement.augmentation E.object)
  let b := evaluateDiagramMap S.sourceAugmentation E.object
  letI := diagramMap_isIso a (fun j => S.cech.replacement.weak E.object
    ((reindex (affineParameterPoint Q F)).obj j))
  letI := diagramMap_isIso b (S.sourceWeak E.object)
  letI := diagramMap_isIso S.span.scalarUnit T.scalarUnitWeak
  exact q.map (injectiveExteriorCoefficientCone S) ≫ inv (q.map a) ≫ inv (q.map b) ≫
    q.map (exteriorScalarDiagramMap S) ≫ inv (q.map S.span.scalarUnit) ≫
    q.map (polynomialToQA S.span) ≫ q.map (Functor.whiskerRight P.ordinary.map (coefficientWeightFunctor k))

/-- For a commutative $\mathbb{Q}$-algebra $k$, a coherent exterior cone for the universal exterior
families `B`: exterior coefficient data `source` with a normalization (`FullExteriorNormalization`)
and, for every weight-$2$ negative cyclic diagram `NC` and every global model `P` of it over the
affine parameter prestack, a cone `map P` from the constant diagram at the global-sections complex
`globalHom G E.object` of the exterior square $E$ of the cotangent complex to the replacement of the
weight-$2$ de Rham diagram shifted by $-2$ (`P.ordinary.diagram ⋙ coefficientWeightFunctor k`),
whose image in the localized category of diagrams is the class
`exteriorInjectiveDiagramClass source normalization P` (a composite in the localized category that
starts from the global-sections cone into the injective exterior coefficient diagram and passes
through the exterior map). -/
structure CoherentExteriorCone {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} (B : UniversalExteriorFamilies D L F G CY H E) where
  source : ExteriorCoefficientSources B
  normalization : FullExteriorNormalization source
  map : ∀ {NC : NegativeCyclicDiagram D.functor (2 : ℤ)}
    (P : GlobalNCModel D 2 NC (affineParameterPrestack Q F)),
    (Functor.const (Families (affineParameterPrestack Q F))).obj (globalHom G E.object) ⟶
      P.ordinary.diagram ⋙ coefficientWeightFunctor k
  normalized : ∀ {NC : NegativeCyclicDiagram D.functor (2 : ℤ)}
    (P : GlobalNCModel D 2 NC (affineParameterPrestack Q F)),
    (diagramQ (LargeScalar k) (Families (affineParameterPrestack Q F))).map (map P) =
      exteriorInjectiveDiagramClass source normalization P

/-- Native limit lift of the injective target cone computes the global map. -/
def parameterExteriorComparison {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {L : CochainLiftModel k} {F : Prestack k} {G : QCohEnhancement M U F}
    {CY : CotangentContext R G} {H : CoherentMonoidalEnhancement G}
    {E : ExteriorSquare H CY.cotangent.object} {B : UniversalExteriorFamilies D L F G CY H E}
    (C : CoherentExteriorCone B) {NC : NegativeCyclicDiagram D.functor (2 : ℤ)}
    (P : GlobalNCModel D 2 NC (affineParameterPrestack Q F))
    [PreservesLimit P.ordinary.diagram (coefficientWeightFunctor k)] :
    globalHom G E.object ⟶ ((globalToCoefficients k).obj (weightComplex P))⟦-2⟧ :=
  limit.lift (P.ordinary.diagram ⋙ coefficientWeightFunctor k)
    ⟨globalHom G E.object, C.map P⟩ ≫
      (preservesLimitIso (coefficientWeightFunctor k) P.ordinary.diagram).inv

end MathlibExt.AlgebraicGeometry.DerivedCoherentExteriorDiagrams
