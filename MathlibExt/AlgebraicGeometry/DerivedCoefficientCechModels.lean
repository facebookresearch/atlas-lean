/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
public import MathlibExt.AlgebraicGeometry.DerivedScalarUnitModels
public import MathlibExt.CategoryTheory.DGMoritaClosedModels
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic

/-!
# Enriched coefficient diagrams and the actual global-section comparison

The coefficient input consists of native DG sections over the complete
family coefficient category. Its cochain diagram has the literal
section values and the actual arrow-generator action. An injective
replacement is made in the whole diagram category before taking its
native limit. The all-E functor and all its homogeneous maps are fixed
by the limit projections of that one enriched replacement.

The comparison from RHom(O_X,E) is fixed on every homogeneous cochain:
apply the enriched coefficient functor to that cochain and evaluate on
the actual coefficient-unit cone. Fixing only the identity in each
affine coefficient complex would not fix higher descent cohomology.
Quasi-isomorphism and coherent QCoh realization are separate source
construction/proof dependencies, not fields of this comparison.

References: PTVV arXiv:1111.3209v4, Definition 2.1 and pp.30–31;
HAG II math/0404373v7, §§1.3.7 and 1.4.1; enriched Yoneda.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle

universe u v w

section Evaluation
variable {R : Type u} [CommRing R] {A : Type u} [DGCategory R A]

/-- The literal closed component of a native DG natural transformation. -/
def evaluationMap {F H : DGFunctor R A (Cochains R)} (f : F ⟶ H) (E : A) :
    F.toEnrichedFunctor.obj E ⟶ H.toEnrichedFunctor.obj E :=
  Cocycle.homOf (Cocycle.mk (f.dgApp E) 1 rfl (by
    have h := f.dgApp_mem_dgCycles E
    rw [mem_dgCycles] at h
    simpa only [dgDifferential_linearHomComplex, zero_add] using! h))

@[simp] theorem evaluationMap_id (F : DGFunctor R A (Cochains R)) (E : A) :
    evaluationMap (𝟙 F) E = 𝟙 _ := by
  apply (Cocycle.equivHom _ _).injective
  ext1
  change Cochain.ofHom (evaluationMap (𝟙 F) E) = Cochain.ofHom (𝟙 _)
  rw [evaluationMap, Cocycle.cochain_ofHom_homOf_eq_coe]
  change (DGNatTrans.id F.toEnrichedFunctor).dgApp E = _
  rw [DGNatTrans.dgApp_id, dgId_linearHomComplex]

@[simp] theorem evaluationMap_comp {F H I : DGFunctor R A (Cochains R)}
    (f : F ⟶ H) (g : H ⟶ I) (E : A) :
    evaluationMap (f ≫ g) E = evaluationMap f E ≫ evaluationMap g E := by
  ext1 n
  change ((DGNatTrans.comp f g).dgApp E : Cochain _ _ 0).v n n _ =
    (f.dgApp E : Cochain _ _ 0).v n n _ ≫ (g.dgApp E : Cochain _ _ 0).v n n _
  rw [DGNatTrans.dgApp_comp, dgCompZero_def, dgComp_linearHomComplex]
  simp only [mul_zero, Int.negOnePow_zero, one_smul]
  exact Cochain.comp_v _ _ _ n n n _ _

/-- Evaluation preserves the whole ordinary diagram and its actual cochain maps. -/
def evaluateDiagram {J : Type v} [Category.{w} J]
    (D : J ⥤ DGFunctor R A (Cochains R)) (E : A) : J ⥤ Cochains R where
  obj j := (D.obj j).toEnrichedFunctor.obj E
  map f := evaluationMap (D.map f) E
  map_id j := by simp
  map_comp f g := by simp

/-- The augmentation of one enriched diagram, evaluated at the same E. -/
def evaluateDiagramMap {J : Type v} [Category.{w} J]
    {D H : J ⥤ DGFunctor R A (Cochains R)} (a : D ⟶ H) (E : A) :
    evaluateDiagram D E ⟶ evaluateDiagram H E where
  app j := evaluationMap (a.app j) E
  naturality i j f := by
    change evaluationMap (D.map f) E ≫ evaluationMap (a.app j) E =
      evaluationMap (a.app i) E ≫ evaluationMap (H.map f) E
    rw [← evaluationMap_comp, ← evaluationMap_comp, a.naturality]

/-- The genuine injective lifting property in a whole cochain diagram category. -/
def IsInjectivelyFibrant {J : Type v} [Category.{w} J] (D : J ⥤ Cochains R) : Prop :=
  ∀ (U V : J ⥤ Cochains R) (i : U ⟶ V),
    (∀ j, Mono (i.app j) ∧ QuasiIso (i.app j)) →
      ∀ f : U ⟶ D, ∃ g : V ⟶ D, i ≫ g = f

/-- A genuine injective replacement of a fixed full cochain diagram. -/
structure InjectiveDiagramReplacement {J : Type v} [Category.{w} J]
    (D : J ⥤ Cochains R) where
  diagram : J ⥤ Cochains R
  augmentation : D ⟶ diagram
  mono : ∀ j, Mono (augmentation.app j)
  weak : ∀ j, QuasiIso (augmentation.app j)
  fibrant : IsInjectivelyFibrant diagram

/-- The actual localization of whole cochain diagrams at objectwise quasi-isomorphisms. -/
def diagramWeakEquivalences (R : Type u) [CommRing R] (J : Type v) [Category.{w} J] :
    MorphismProperty (J ⥤ Cochains R) := fun _ _ a => ∀ j, QuasiIso (a.app j)

abbrev diagramQ (R : Type u) [CommRing R] (J : Type v) [Category.{w} J] :=
  (diagramWeakEquivalences R J).Q

end Evaluation

variable {k : Type u} [CommRing k] {L : CochainLiftModel k}
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {X : Prestack k}
    (C : FamilyCoefficientCategory L N X) (G : QCohEnhancement M U X)

/-- An actual all-E coefficient system, retaining the native DG module action
and all homogeneous natural maps. -/
structure CoefficientDiagramSystem where
  sections : letI := C.enrichment
    EnrichedFunctor (Cochains (LargeScalar k)) G.category (CoefficientSection C)
  diagram : Families X ⥤ DGFunctor (LargeScalar k) G.category (Cochains (LargeScalar k))
  value : letI := C.enrichment
    ∀ (E : G.category) (j : Families X),
    (diagram.obj j).toEnrichedFunctor.obj E = (sections.obj E).toEnrichedFunctor.obj j
  homogeneous : letI := C.enrichment
    ∀ (E F : G.category) (p : ℤ) (f : DGHom (LargeScalar k) p E F)
    (j : Families X),
    HEq ((diagram.obj j).toEnrichedFunctor.dgMap p f)
      (DGFunctor.dgApp (LargeScalar k) p j (sections.dgMap p f))
  transport : letI := C.enrichment
    ∀ (E : G.category) (j l : Families X) (f : j ⟶ l),
    HEq (Cochain.ofHom ((evaluateDiagram diagram E).map f))
      ((sections.obj E).toEnrichedFunctor.dgMap 0
        (generator C f 0
          (dgId (LargeScalar k) (op (coefficientObject L N ((algebraProjection X).obj l))))))

/-- The enriched replacement is one actual all-E diagram; the whole
diagram lifting property is checked for every E. -/
structure EnrichedDiagramReplacement (D : CoefficientDiagramSystem C G) where
  diagram : Families X ⥤ DGFunctor (LargeScalar k) G.category (Cochains (LargeScalar k))
  augmentation : D.diagram ⟶ diagram
  mono : ∀ (E : G.category) (j : Families X),
    Mono ((evaluateDiagramMap augmentation E).app j)
  weak : ∀ (E : G.category) (j : Families X),
    QuasiIso ((evaluateDiagramMap augmentation E).app j)
  fibrant : ∀ E : G.category, IsInjectivelyFibrant (evaluateDiagram diagram E)

/-- The actual homotopy-limit coefficient complex of E. -/
def coefficientLimit {D : CoefficientDiagramSystem C G}
    (B : EnrichedDiagramReplacement C G D) (E : G.category) : Cochains (LargeScalar k) :=
  limit (evaluateDiagram B.diagram E)

/-- Enriched global coefficients are normalized by every native limit projection,
for every E-map in every homogeneous degree. -/
structure CoefficientLimitFunctor {D : CoefficientDiagramSystem C G}
    (B : EnrichedDiagramReplacement C G D) where
  functor : EnrichedFunctor (Cochains (LargeScalar k)) G.category (Cochains (LargeScalar k))
  comparison : ∀ E : G.category, functor.obj E ≅ coefficientLimit C G B E
  projection : ∀ (E F : G.category) (p : ℤ) (f : DGHom (LargeScalar k) p E F)
    (j : Families X) (i : ℤ),
    (functor.dgMap p f : Cochain (functor.obj E) (functor.obj F) p).v i (i + p) rfl ≫
      ((comparison F).hom ≫ limit.π (evaluateDiagram B.diagram F) j).f (i + p) =
    ((comparison E).hom ≫ limit.π (evaluateDiagram B.diagram E) j).f i ≫
      ((B.diagram.obj j).toEnrichedFunctor.dgMap p f :
        Cochain _ _ p).v i (i + p) rfl

/-- The unit is augmented to the actual coefficient diagram by a quasi-isomorphism.
Its local resolutions may have positive acyclic terms; replacing this by
an isomorphism would lose coherent descent classes in higher degrees. -/
structure UnitCoefficientDiagram (D : CoefficientDiagramSystem C G) where
  coefficients : Families X ⥤ Cochains (LargeScalar k)
  value : ∀ j : Families X, coefficients.obj j =
      affineCoefficient L N ((algebraProjection X).obj j)
  map : ∀ (j l : Families X) (f : j ⟶ l),
    HEq (coefficients.map f) (affineCoefficientMap L N ((algebraProjection X).map f))
  augmentation : evaluateDiagram D.diagram G.unit ⟶ coefficients
  weak : ∀ j : Families X, QuasiIso (augmentation.app j)
  unit : (Functor.const (Families X)).obj (𝟙_ (Cochains (LargeScalar k))) ⟶ coefficients
  unit_normalized : ∀ j : Families X,
    HEq (unit.app j) (affineCoefficientUnit L N ((algebraProjection X).obj j))

/-- The comparison lift has its actual augmentation square fixed on the whole diagram. -/
structure UnitCoefficientLift {D : CoefficientDiagramSystem C G}
    (B : EnrichedDiagramReplacement C G D) (V : UnitCoefficientDiagram C G D) where
  replacement : InjectiveDiagramReplacement V.coefficients
  map : evaluateDiagram B.diagram G.unit ⟶ replacement.diagram
  square : evaluateDiagramMap B.augmentation G.unit ≫ map =
    V.augmentation ≫ replacement.augmentation

/-- The coherent unit cone is fixed as a class in the localization of whole
diagrams, after the actual unit comparison. It is not chosen chart by chart. -/
structure CoherentUnitCone {D : CoefficientDiagramSystem C G}
    {B : EnrichedDiagramReplacement C G D} {V : UnitCoefficientDiagram C G D}
    (T : UnitCoefficientLift C G B V) where
  cone : (Functor.const (Families X)).obj (𝟙_ (Cochains (LargeScalar k))) ⟶
    evaluateDiagram B.diagram G.unit
  normalized : (diagramQ (LargeScalar k) (Families X)).map (cone ≫ T.map) =
    (diagramQ (LargeScalar k) (Families X)).map (V.unit ≫ T.replacement.augmentation)

/-- The coherent unit uses the native limit lift of the normalized full cone. -/
def limitUnit {D : CoefficientDiagramSystem C G} {B : EnrichedDiagramReplacement C G D}
    {V : UnitCoefficientDiagram C G D} {T : UnitCoefficientLift C G B V}
    (I : CoherentUnitCone C G T) :
    (𝟙_ (Cochains (LargeScalar k))) ⟶ coefficientLimit C G B G.unit :=
  limit.lift (evaluateDiagram B.diagram G.unit)
    ⟨𝟙_ (Cochains (LargeScalar k)), I.cone⟩

/-- The genuine global unit in the same enriched limit model. -/
def globalUnit {D : CoefficientDiagramSystem C G} {B : EnrichedDiagramReplacement C G D}
    (H : CoefficientLimitFunctor C G B) {V : UnitCoefficientDiagram C G D}
    {T : UnitCoefficientLift C G B V} (I : CoherentUnitCone C G T) :
    (𝟙_ (Cochains (LargeScalar k))) ⟶ H.functor.obj G.unit :=
  limitUnit C G I ≫ (H.comparison G.unit).inv

/-- The all-degree comparison is fixed by enriched Yoneda evaluation on
the actual coherent coefficient unit. Quasi-isomorphism is separate. -/
structure GlobalSectionComparison {D : CoefficientDiagramSystem C G}
    {B : EnrichedDiagramReplacement C G D} (H : CoefficientLimitFunctor C G B)
    {V : UnitCoefficientDiagram C G D} {T : UnitCoefficientLift C G B V}
    (I : CoherentUnitCone C G T) where
  map : ∀ E : G.category, globalHom G E ⟶ H.functor.obj E
  normalized : ∀ (E : G.category) (p : ℤ) (f : DGHom (LargeScalar k) p G.unit E),
    ((map E).f p).hom f =
      ((H.functor.dgMap p f : Cochain _ _ p).v 0 p (zero_add p)).hom
        (((globalUnit C G H I).f 0).hom
          ((HomologicalComplex.singleObjXSelf (.up ℤ) 0
            (𝟙_ (ModuleCat.{u + 1} (LargeScalar k)))).inv 1))
  natural : ∀ (E F : G.category) (p : ℤ) (f : DGHom (LargeScalar k) p E F) (i : ℤ),
    (dgPostcomp (LargeScalar k) (op G.unit) p f :
      Cochain (globalHom G E) (globalHom G F) p).v i (i + p) rfl ≫ (map F).f (i + p) =
    (map E).f i ≫ (H.functor.dgMap p f : Cochain _ _ p).v i (i + p) rfl

/-- The actual comparison into the native coefficient homotopy limit. -/
def globalSectionMap {D : CoefficientDiagramSystem C G}
    {B : EnrichedDiagramReplacement C G D} {H : CoefficientLimitFunctor C G B}
    {V : UnitCoefficientDiagram C G D} {T : UnitCoefficientLift C G B V}
    {I : CoherentUnitCone C G T} (P : GlobalSectionComparison C G H I)
    (E : G.category) : globalHom G E ⟶ coefficientLimit C G B E :=
  P.map E ≫ (H.comparison E).hom

end MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
