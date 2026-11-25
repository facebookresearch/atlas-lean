/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
public import MathlibExt.AlgebraicGeometry.CoherentNerveTransformations
public import MathlibExt.AlgebraicTopology.SimplicialCovariantModels

/-!
# Whole source coefficient realizations

The coefficient image has G-indexed objects and the actual enriched
Hom of their DG coefficient modules. Augmented source objects retain
the actual small semilinear family, every homogeneous action equation,
and a quasi-isomorphism of whole coefficient diagrams. Their morphisms
carry both actual maps and the native augmentation square.

The projection to cofibrant geometric coefficient modules is required
to be a categorical localization of this actual augmentation category.
The geometric realization agrees with the raw localization on the
entire source category, by one natural equivalence of whole functors.
The resulting comparison to G.realization is likewise a full-functor
comparison. Independent objectwise equivalences do not supply it.

References: Keller, Deriving DG categories, §§1/6; HAG II
math/0404373v7 §1.3.7; Lurie HTT §§2.2 and 3.3.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
open MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
open MathlibExt.AlgebraicGeometry.CoherentNerveTransformations
open scoped Simplicial

universe u v w

/-- Canonical value lifting of every simplex and every simplicial map. -/
def liftSet (X : SSet.{v}) : SSet.{max v w} where
  obj n := ULift.{w} (X.obj n)
  map f := ↾fun x => ULift.up (X.map f x.down)
  map_id n := by ext x; simp
  map_comp f g := by ext x; simp

/-- The actual functorial value lift of a simplicial map. -/
def liftSetMap {X Y : SSet.{v}} (f : X ⟶ Y) : liftSet.{v, w} X ⟶ liftSet.{v, w} Y where
  app n := ↾fun x => ULift.up (f.app n x.down)
  naturality n m g := by ext x; exact congrArg ULift.up (congrArg (fun t => t x.down) (f.naturality g))

section ObjectLift
variable {R : Type v} [CommRing R] (C : Type w) [DGCategory R C]

/-- Object lifting preserves the original Hom, unit, differential and composition. -/
@[instance_reducible] def objectLiftEnrichment : DGCategory R (ULift.{u} C) where
  Hom x y := dgHomComplex R x.down y.down
  id x := eId (Cochains R) x.down
  comp x y z := eComp (Cochains R) x.down y.down z.down
  id_comp x y := EnrichedCategory.id_comp (V := Cochains R) x.down y.down
  comp_id x y := EnrichedCategory.comp_id (V := Cochains R) x.down y.down
  assoc x y z t := EnrichedCategory.assoc (V := Cochains R) x.down y.down z.down t.down

attribute [local instance] objectLiftEnrichment

/-- The actual DG down functor changes no homogeneous map. -/
def objectDown : EnrichedFunctor (Cochains R) (ULift.{u} C) C where
  obj x := x.down
  map _ _ := 𝟙 _

/-- Native simplicial enrichment transport, with independent object universes. -/
def heterogeneousSimplicialFunctor {A : Type w} {B : Type u}
    [DGCategory R A] [DGCategory R B] (F : EnrichedFunctor (Cochains R) A B) :
    EnrichedFunctor SSet.{v} (DGSimplicial (k := R) A) (DGSimplicial (k := R) B) :=
  forgetFunctor ((transportFunctor (cochainToSSet R) F.op).op)

/-- The whole lifted-nerve map is fixed by the actual frame down functor. -/
structure ObjectNerveLift where
  map : dgNerve (k := R) (ULift.{u} C) ⟶ liftSet.{max v w, u} (dgNerve (k := R) C)
  normalized : ∀ (n : SimplexCategoryᵒᵖ) (a : (dgNerve (k := R) (ULift.{u} C)).obj n),
    (map.app n a).down = a.comp SSet (heterogeneousSimplicialFunctor (objectDown C))

/-- Native frame postcomposition supplies the completed whole object-universe comparison. -/
def objectNerveLift : ObjectNerveLift.{u, v, w} (R := R) C where
  map :=
    { app n := ↾fun a => ULift.up
        (a.comp SSet (heterogeneousSimplicialFunctor (objectDown C)))
      naturality n m f := by
        ext a
        apply congrArg ULift.up
        exact EnrichedFunctor.comp_assoc (V := SSet) _ _ _ }
  normalized _ _ := rfl

end ObjectLift

variable {k : Type u} [CommRing k] {L : CochainLiftModel k}
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M} {X : Prestack k}
    (C : FamilyCoefficientCategory L N X)

/-- Underlying ordinary diagrams retain every literal coefficient-section value and map. -/
structure SectionDiagrams where
  functor : CoefficientSection C ⥤ (Families X ⥤ Cochains (LargeScalar k))
  value : letI := C.enrichment
    ∀ (E : CoefficientSection C) (j : Families X),
    (functor.obj E).obj j = E.toEnrichedFunctor.obj j
  transport : letI := C.enrichment
    ∀ (E : CoefficientSection C) (j l : Families X) (f : j ⟶ l),
    HEq (CochainComplex.HomComplex.Cochain.ofHom ((functor.obj E).map f))
      (E.toEnrichedFunctor.dgMap 0 (generator C f 0
        (dgId (LargeScalar k) (op (coefficientObject L N ((algebraProjection X).obj l))))))
  map : letI := C.enrichment
    ∀ (E F : CoefficientSection C) (a : E ⟶ F) (j : Families X),
    HEq ((functor.map a).app j) (evaluationMap a j)

variable (R : RawModuleRealization M) (B : SectionDiagrams C)

/-- Actual small geometric augmentation data for one native coefficient section. -/
structure SmallGeometricAugmentation (E : CoefficientSection C) where
  raw : Families X ⥤ AffineModulePoint N
  base : raw ⋙ moduleProjection N = algebraProjection X
  augmentation : B.functor.obj E ⟶ rawCoefficientDiagram raw
  weak : ∀ j : Families X, QuasiIso (augmentation.app j)
  action : letI := C.enrichment
    ∀ (j l : Families X) (f : j ⟶ l) (p q r : ℤ) (h : q + p = r)
      (a : (N.functor.obj ((algebraProjection X).obj l)).X.X p)
      (m : (E.toEnrichedFunctor.obj j).X q),
    HEq
      (((augmentation.app l).f r).hom
        (((eqToHom (B.value E l).symm).f r).hom
          ((E.toEnrichedFunctor.dgMap p (generator C f p (ULift.up a)) :
            CochainComplex.HomComplex.Cochain _ _ p).v q r h m)))
      (ULift.up.{u + 1} (MathlibExt.AlgebraicGeometry.DerivedCotangentModels.moduleAction
        (raw.obj l).module (op PUnit.unit)
        (((N.functor.map (eqToHom
          (congrArg (fun F => F.obj l) base).symm)).hom.f p).hom a) h
        (((raw.map f).map.f q).hom
          ((((augmentation.app j).f q).hom
            ((eqToHom (B.value E j).symm).f q m)).down))))
  cocartesian : ∀ e : (nerve (Families X)) _⦋1⦌,
    IsCocartesianEdge M.projection ((nerveMap raw ≫ R.map).app (op ⦋1⦌) e)

/-- A source augmentation keeps its actual coefficient section and projective cofibrancy. -/
structure AugmentedSection where
  object : CoefficientSection C
  cofibrant : IsCofibrantSection C object
  data : SmallGeometricAugmentation C R B object

/-- Actual pairs of maps commute with the entire native augmentation diagram. -/
structure AugmentedSectionMap (E F : AugmentedSection C R B) where
  map : E.object ⟶ F.object
  raw : E.data.raw ⟶ F.data.raw
  base : Functor.whiskerRight raw (moduleProjection N) =
    eqToHom (E.data.base.trans F.data.base.symm)
  square : B.functor.map map ≫ F.data.augmentation =
    E.data.augmentation ≫
      Functor.whiskerRight (Functor.whiskerRight raw (coefficientProjection N)) (largeCochainLift k)

/-- The native identity pair preserves the same actual augmentation. -/
def augmentedId (E : AugmentedSection C R B) : AugmentedSectionMap C R B E E where
  map := 𝟙 _
  raw := 𝟙 _
  base := by simp
  square := by
    ext j i
    simp
    exact (ModuleCat.id_apply _ _).symm

/-- Composition is the literal pair of native module and raw-family maps. -/
def augmentedComp {E F G : AugmentedSection C R B}
    (a : AugmentedSectionMap C R B E F) (b : AugmentedSectionMap C R B F G) :
    AugmentedSectionMap C R B E G where
  map := a.map ≫ b.map
  raw := a.raw ≫ b.raw
  base := by rw [Functor.whiskerRight_comp, a.base, b.base]; simp
  square := by
    rw [B.functor.map_comp, Category.assoc, b.square, ← Category.assoc, a.square]
    simp only [Functor.whiskerRight_comp, Category.assoc]

/-- A morphism is determined by its two actual maps. -/
theorem augmentedMap_ext {E F : AugmentedSection C R B}
    {a b : AugmentedSectionMap C R B E F} (h : a.map = b.map) (g : a.raw = b.raw) : a = b := by
  cases a
  cases b
  cases h
  cases g
  rfl

/-- The actual augmentation category, without a chosen geometric target functor. -/
instance : Category (AugmentedSection C R B) where
  Hom E F := AugmentedSectionMap C R B E F
  id := augmentedId C R B
  comp := augmentedComp C R B
  id_comp _a := augmentedMap_ext C R B (Category.id_comp _) (Category.id_comp _)
  comp_id _a := augmentedMap_ext C R B (Category.comp_id _) (Category.comp_id _)
  assoc _a _b _c := augmentedMap_ext C R B (Category.assoc _ _ _) (Category.assoc _ _ _)

/-- The raw source functor keeps every actual family natural transformation. -/
def augmentedRaw : AugmentedSection C R B ⥤ (Families X ⥤ AffineModulePoint N) where
  obj E := E.data.raw
  map a := a.raw

/-- The actual full joint raw simplex, including all augmentation-category parameters. -/
def augmentedRawDegree (n m : SimplexCategoryᵒᵖ)
    (a : (nerve (AugmentedSection C R B)).obj n) (g : n ⟶ m)
    (b : (nerve (Families X)).obj m) : (nerve (AffineModulePoint N)).obj m :=
  (a.whiskerLeft (SimplexCategory.toCat.map g.unop).toFunctor).prod' b ⋙
    Functor.uncurry.obj (augmentedRaw C R B)

/-- Every geometric coefficient object is an actual cofibrant native section with such data. -/
def IsGeometricCoefficient (E : CoefficientSection C) : Prop :=
  IsCofibrantSection C E ∧ Nonempty (SmallGeometricAugmentation C R B E)

/-- Its enhanced full subcategory retains the actual DG-natural module Hom. -/
abbrev GeometricCoefficients :=
  letI := C.enrichment
  DGFullSubcategory (IsGeometricCoefficient C R B)

/-- The ordinary source category uses the same literal closed module transformations. -/
instance : Category (GeometricCoefficients C R B) where
  Hom E F := E.obj ⟶ F.obj
  id E := 𝟙 E.obj
  comp a b := a ≫ b
  id_comp a := Category.id_comp a
  comp_id a := Category.comp_id a
  assoc a b c := Category.assoc a b c

/-- Projection forgets augmentation choices, retaining the actual module map. -/
def geometricProjection : AugmentedSection C R B ⥤ GeometricCoefficients C R B where
  obj E := ⟨E.object, E.cofibrant, ⟨E.data⟩⟩
  map a := a.map

/-- A native closed geometric module map has its actual DG closed class. -/
def geometricCycle {E F : GeometricCoefficients C R B} (a : E ⟶ F) :
    letI := C.enrichment; dgCycles (LargeScalar k) E F := by
  letI := C.enrichment
  let z := DGFunctor.homEquivDGCycles (LargeScalar k) E.obj F.obj a
  have e : dgHomComplex (LargeScalar k) E F = dgHomComplex (LargeScalar k) E.obj F.obj :=
    DGFullSubcategory.dgHomComplex_eq (LargeScalar k) E F
  let i := (eqToIso e).inv
  refine ⟨(i.f 0).hom z.val, ?_⟩
  rw [mem_dgCycles]
  have h := congrArg (fun f => f.hom z.val) (i.comm 0 1)
  have hz := (mem_dgCycles (LargeScalar k)).mp z.property
  change (((dgHomComplex (LargeScalar k) E F).d 0 1).hom) ((i.f 0).hom z.val) = 0
  change (((i.f 1).hom) ((dgDifferential (LargeScalar k) 0) z.val)) =
    (((dgHomComplex (LargeScalar k) E F).d 0 1).hom) ((i.f 0).hom z.val) at h
  rw [hz, map_zero] at h
  exact h.symm

/-- The native coherent nerve of this full DG module category. -/
def geometricNerve : SSet.{u + 2} := by
  letI := C.enrichment
  exact dgNerve (k := LargeScalar k) (GeometricCoefficients C R B)

/-- The ordinary closed-functor comparison is fixed on every object and actual module map. -/
structure GeometricClosedFunctor where
  functor : letI := C.enrichment; GeometricCoefficients C R B ⥤
    DGSimplicial (k := LargeScalar k) (GeometricCoefficients C R B)
  object : letI := C.enrichment; ∀ E : GeometricCoefficients C R B,
    functor.obj E = ForgetEnrichment.of SSet (DGSimplicialCategory.of (LargeScalar k) E)
  map : letI := C.enrichment; ∀ (E F : GeometricCoefficients C R B) (a : E ⟶ F),
    HEq (functor.map a) (simplicialArrow (geometricCycle C R B a))

/-- The canonical ordinary augmentation-nerve comparison uses native simplicial thickening. -/
def augmentationNerve (F : GeometricClosedFunctor C R B) :
    nerve (AugmentedSection C R B) ⟶ geometricNerve C R B := by
  letI := C.enrichment
  exact nerveMap (geometricProjection C R B ⋙ F.functor) ≫
    SimplicialNerve.fromNerve (DGSimplicial (k := LargeScalar k) (GeometricCoefficients C R B))

/-- The actual weak maps of the augmentation category, measured on every affine coefficient. -/
def IsAugmentationWeak {E F : AugmentedSection C R B} (a : E ⟶ F) : Prop :=
  ∀ j : Families X, QuasiIso ((B.functor.map a.map).app j)

/-- An actual functor from the augmentation source inverts these native weak maps. -/
def InvertsAugmentationWeak (Z : SSet.{u + 2}) (a : (mapping (nerve (AugmentedSection C R B)) Z) _⦋0⦌) : Prop :=
  ∀ (E F : AugmentedSection C R B) (f : E ⟶ F), IsAugmentationWeak C R B f →
    IsEquivalenceEdge Z
      (((SimplicialCategory.homEquiv' _ _).symm a).app (op ⦋1⦌) (nerve.edgeMk f).edge)

/-- Full categorical localization pins every coherent module simplex, rather than H0 alone. -/
structure GeometricCoefficientLocalization (F : GeometricClosedFunctor C R B) where
  invert : ∀ (E G : AugmentedSection C R B) (a : E ⟶ G), IsAugmentationWeak C R B a →
    IsEquivalenceEdge (geometricNerve C R B)
      ((augmentationNerve C R B F).app (op ⦋1⦌) (nerve.edgeMk a).edge)
  universal : ∀ (Z : SSet.{u + 2}) [SSet.Quasicategory Z],
    ∃ f : mapping (geometricNerve C R B) Z ⟶
      ((mapping (nerve (AugmentedSection C R B)) Z).fullEnhancedSubcategory
        (InvertsAugmentationWeak C R B Z)).toSSet,
      f ≫ (SSet.Subcomplex.ι _) = precomposition (augmentationNerve C R B F) Z ∧
        CategoricalWeakEquivalence f

/-- The raw geometric functor is fixed on every joint source/family simplex. -/
structure RawGeometricRealization where
  map : nerve (AugmentedSection C R B) ⟶ liftSet.{u + 1, u + 2} (qcoh M X)
  normalized : ∀ (n m : SimplexCategoryᵒᵖ)
    (a : (nerve (AugmentedSection C R B)).obj n) (g : n ⟶ m)
    (b : (nerve (Families X)).obj m),
    (((map.app n a).down.val.app m g) b) = R.map.app m (augmentedRawDegree C R B n m a g b)

/-- Native coefficient geometry agrees with this whole raw functor after actual localization. -/
structure GeometricCoefficientRealization (F : GeometricClosedFunctor C R B)
    (P : GeometricCoefficientLocalization C R B F) (T : RawGeometricRealization C R B) where
  map : geometricNerve C R B ⟶
    liftSet.{u + 1, u + 2} (qcoh M X)
  weak : CategoricalWeakEquivalence map
  comparison : SSet.Edge (X := mapping (nerve (AugmentedSection C R B))
      (liftSet.{u + 1, u + 2} (qcoh M X)))
    ((SimplicialCategory.homEquiv' _ _) (augmentationNerve C R B F ≫ map))
    ((SimplicialCategory.homEquiv' _ _) T.map)
  equivalence : IsEquivalenceEdge _ comparison.edge

/-- G-indexed source objects in the universe of all native coefficient sections. -/
structure CoefficientImage (G : QCohEnhancement M U X) (D : CoefficientDiagramSystem C G) :
    Type (u + 2) where
  object : G.category

/-- The image Hom is the literal full DG-natural coefficient-section Hom. -/
instance imageEnrichment (G : QCohEnhancement M U X) (D : CoefficientDiagramSystem C G) :
    DGCategory (LargeScalar k) (CoefficientImage C G D) := by
  letI := C.enrichment
  exact
    { Hom x y := dgHomComplex (LargeScalar k) (D.sections.obj x.object) (D.sections.obj y.object)
      id x := eId (Cochains (LargeScalar k)) (D.sections.obj x.object)
      comp x y z := eComp (Cochains (LargeScalar k))
        (D.sections.obj x.object) (D.sections.obj y.object) (D.sections.obj z.object)
      id_comp x y := EnrichedCategory.id_comp (V := Cochains (LargeScalar k))
        (D.sections.obj x.object) (D.sections.obj y.object)
      comp_id x y := EnrichedCategory.comp_id (V := Cochains (LargeScalar k))
        (D.sections.obj x.object) (D.sections.obj y.object)
      assoc x y z t := EnrichedCategory.assoc (V := Cochains (LargeScalar k))
        (D.sections.obj x.object) (D.sections.obj y.object)
        (D.sections.obj z.object) (D.sections.obj t.object) }

/-- The source image functor is exactly D.sections on every Hom complex. -/
def imageFunctor (G : QCohEnhancement M U X) (D : CoefficientDiagramSystem C G) :
    letI := objectLiftEnrichment.{u + 2} (R := LargeScalar k) G.category
    EnrichedFunctor (Cochains (LargeScalar k)) (ULift.{u + 2} G.category) (CoefficientImage C G D) := by
  letI := objectLiftEnrichment.{u + 2} (R := LargeScalar k) G.category
  letI := C.enrichment
  exact
    { obj x := ⟨x.down⟩
      map x y := D.sections.map x.down y.down
      map_id x := D.sections.map_id x.down
      map_comp x y z := D.sections.map_comp x.down y.down z.down }

/-- The image inclusion fixes every actual coefficient object and every homogeneous module map. -/
structure ImageInclusion (G : QCohEnhancement M U X) (D : CoefficientDiagramSystem C G) where
  functor : letI := C.enrichment
    EnrichedFunctor (Cochains (LargeScalar k))
      (CoefficientImage C G D) (GeometricCoefficients C R B)
  object : ∀ x : CoefficientImage C G D, (functor.obj x).obj = D.sections.obj x.object
  map : letI := C.enrichment; ∀ x y : CoefficientImage C G D,
    HEq (functor.map x y)
      (𝟙 (dgHomComplex (LargeScalar k) (D.sections.obj x.object) (D.sections.obj y.object)))

/-- The actual source image geometry and G.realization agree on the entire lifted DG nerve. -/
structure FullCoefficientImageModel (G : QCohEnhancement M U X) (D : CoefficientDiagramSystem C G)
    (F : GeometricClosedFunctor C R B) (P : GeometricCoefficientLocalization C R B F)
    (T : RawGeometricRealization C R B) (K : GeometricCoefficientRealization C R B F P T) where
  inclusion : ImageInclusion C R B G D
  source : ObjectNerveLift.{u + 2, u + 1, u + 1} (R := LargeScalar k) G.category
  comparison : letI := objectLiftEnrichment.{u + 2} (R := LargeScalar k) G.category
    letI := C.enrichment
    SSet.Edge (X := mapping (dgNerve (k := LargeScalar k) (ULift.{u + 2} G.category))
      (liftSet.{u + 1, u + 2} (qcoh M X)))
      ((SimplicialCategory.homEquiv' _ _) (source.map ≫ liftSetMap G.realization))
      ((SimplicialCategory.homEquiv' _ _)
        (dgNerveMap (imageFunctor C G D) ≫ dgNerveMap inclusion.functor ≫ K.map))
  equivalence : letI := objectLiftEnrichment.{u + 2} (R := LargeScalar k) G.category
    letI := C.enrichment
    IsEquivalenceEdge _ comparison.edge

/-- A named full source package, including the enriched Hom and whole geometric functor.
Compatible factories choose this package together with G and its coefficient diagram. -/
structure SourcedCoefficientImageModel (G : QCohEnhancement M U X)
    (D : CoefficientDiagramSystem C G) (V : UnitCoefficientDiagram C G D) where
  source : SourceEnrichedQCohModel C G R D V
  diagrams : SectionDiagrams C
  closed : GeometricClosedFunctor C R diagrams
  localization : GeometricCoefficientLocalization C R diagrams closed
  raw : RawGeometricRealization C R diagrams
  geometry : GeometricCoefficientRealization C R diagrams closed localization raw
  comparison : FullCoefficientImageModel C R diagrams G D closed localization raw geometry

end MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
