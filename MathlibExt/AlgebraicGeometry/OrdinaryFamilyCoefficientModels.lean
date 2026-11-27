/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.OrdinaryConstantCoefficientModels
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels

/-!
# Full ordinary-scheme DG coefficient sections and their native realization

Objects of the indexing category are all actual Spec(R)→X families,
and each arrow is its original ring map and commuting scheme square.
The coefficient DG Hom is the coproduct over these actual arrows of
the target constant-ring normalization. Its identities and composition
are fixed on every homogeneous arrow-labelled generator.

Geometric objects are actual projectively cofibrant DG coefficient
sections augmented to small native semilinear module diagrams. The
augmentation respects every original coefficient action and every
family arrow. A full source localization and one comparison of whole
functors fix the realization into native cocartesian QCoh sections.
Perf then uses the original finite-cell/retract tests at every family.

Sources: Keller, Deriving DG categories, Sections1/2/6; HAGII,
math/0404373v7, Section1.3.7; Bhatt--Mathew1807.04725v4,
Notation5.8/Section5.4. Native DG, nerve and localization operations
retain their exact source revisions and license notices in imports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.OrdinaryFamilyCoefficientModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open CochainComplex.HomComplex
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicGeometry.GeneralArcCoverModels
open MathlibExt.AlgebraicGeometry.OrdinarySchemeModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedFamilyCoefficientCategories
open MathlibExt.AlgebraicGeometry.DerivedCoefficientCechModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientImageModels
open MathlibExt.AlgebraicGeometry.CoherentNerveTransformations
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open scoped Simplicial

variable (L : CochainLiftModel ℤ) (N : ShuffleAlgebraFunctor ℤ) (X : QcqsScheme)

/-- Every actual ordinary family arrow has its own original target-coefficient summand. -/
def arrowCoefficients (j l : Family X) : Cochains (LargeScalar ℤ) :=
  ∐ (fun _f : j ⟶ l => affineCoefficient L N
    ((OrdinarySchemeModuleFamilies.coefficientProjection X).obj l))

/-- The literal native summand inclusion fixes each homogeneous family generator. -/
def coefficientGenerator [DGCategory (LargeScalar ℤ) (Family X)]
    (H : ∀ j l : Family X, dgHomComplex (LargeScalar ℤ) j l ≅ arrowCoefficients L N X j l)
    {j l : Family X} (f : j ⟶ l) (p : ℤ)
    (a : (affineCoefficient L N ((OrdinarySchemeModuleFamilies.coefficientProjection X).obj l)).X p) :
    DGHom (LargeScalar ℤ) p j l :=
  (((Sigma.ι (fun _f : j ⟶ l => affineCoefficient L N
      ((OrdinarySchemeModuleFamilies.coefficientProjection X).obj l)) f ≫ (H j l).inv).f p).hom a)

/-- All coefficient Homs and their semilinear compositions use the original ordinary families. -/
structure FamilyCoefficientCategory where
  [enrichment : DGCategory (LargeScalar ℤ) (Family X)]
  homIso : ∀ j l : Family X, dgHomComplex (LargeScalar ℤ) j l ≅ arrowCoefficients L N X j l
  identity : ∀ j : Family X,
    dgId (LargeScalar ℤ) j = coefficientGenerator L N X homIso (𝟙 j) 0
      (dgId (LargeScalar ℤ) (op (coefficientObject L N
        ((OrdinarySchemeModuleFamilies.coefficientProjection X).obj j))))
  composition : ∀ (j l z : Family X) (f : j ⟶ l) (g : l ⟶ z)
    (p q n : ℤ) (h : p + q = n)
    (a : (affineCoefficient L N ((OrdinarySchemeModuleFamilies.coefficientProjection X).obj l)).X p)
    (b : (affineCoefficient L N ((OrdinarySchemeModuleFamilies.coefficientProjection X).obj z)).X q),
    dgComp (LargeScalar ℤ)
      (coefficientGenerator L N X homIso f p a) (coefficientGenerator L N X homIso g q b) h =
      coefficientGenerator L N X homIso (f ≫ g) n
        (dgComp (LargeScalar ℤ)
          (((affineCoefficientMap L N
            ((OrdinarySchemeModuleFamilies.coefficientProjection X).map g)).f p).hom a) b h)

variable {L N X} (C : FamilyCoefficientCategory L N X)

/-- The original family arrow and coefficient determine the actual DG generator. -/
def generator {j l : Family X} (f : j ⟶ l) (p : ℤ)
    (a : (affineCoefficient L N ((OrdinarySchemeModuleFamilies.coefficientProjection X).obj l)).X p) :
    letI := C.enrichment; DGHom (LargeScalar ℤ) p j l := by
  letI := C.enrichment
  exact coefficientGenerator L N X C.homIso f p a

/-- Full native coefficient sections retain all homogeneous semilinear family actions. -/
abbrev CoefficientSection :=
  letI := C.enrichment
  DGFunctor (LargeScalar ℤ) (Family X) (Cochains (LargeScalar ℤ))

/-- The ordinary diagram is fixed on every source object, arrow and closed module transformation. -/
structure SectionDiagrams where
  functor : CoefficientSection C ⥤ (Family X ⥤ Cochains (LargeScalar ℤ))
  value : letI := C.enrichment
    ∀ (E : CoefficientSection C) (j : Family X),
    (functor.obj E).obj j = E.toEnrichedFunctor.obj j
  transport : letI := C.enrichment
    ∀ (E : CoefficientSection C) (j l : Family X) (f : j ⟶ l),
    HEq (Cochain.ofHom ((functor.obj E).map f))
      (E.toEnrichedFunctor.dgMap 0 (generator C f 0
        (dgId (LargeScalar ℤ) (op (coefficientObject L N
          ((OrdinarySchemeModuleFamilies.coefficientProjection X).obj l))))))
  map : letI := C.enrichment
    ∀ (E F : CoefficientSection C) (a : E ⟶ F) (j : Family X),
    HEq ((functor.map a).app j) (evaluationMap a j)

/-- Actual projective cofibrancy is tested against all native componentwise trivial fibrations. -/
def IsCofibrantSection (E : CoefficientSection C) : Prop :=
  letI := C.enrichment
  ∀ (A B : CoefficientSection C) (p : A ⟶ B),
    (∀ j : Family X, QuasiIso (evaluationMap p j) ∧
      ∀ n : ℤ, Function.Surjective ((evaluationMap p j).f n)) →
    ∀ f : E ⟶ B, ∃ g : E ⟶ A, g ≫ p = f

/-- The source small diagram uses the actual constant coefficient modules on all ordinary families. -/
def rawCoefficientDiagram (D : Family X ⥤ AffineModulePoint N) :
    Family X ⥤ Cochains (LargeScalar ℤ) :=
  D ⋙ DerivedSquareZeroFamilies.coefficientProjection N ⋙ largeCochainLift ℤ

variable {S : AffineScalarSystem N} (M : AffineModuleFibration N S)
  (R : RawModuleRealization M) (B : SectionDiagrams C)

/-- A geometric augmentation fixes every scalar, homogeneous map, family arrow and base-change edge. -/
structure SmallGeometricAugmentation (E : CoefficientSection C) where
  raw : Family X ⥤ AffineModulePoint N
  base : raw ⋙ moduleProjection N = OrdinarySchemeModuleFamilies.coefficientProjection X
  augmentation : B.functor.obj E ⟶ rawCoefficientDiagram raw
  weak : ∀ j : Family X, QuasiIso (augmentation.app j)
  action : letI := C.enrichment
    ∀ (j l : Family X) (f : j ⟶ l) (p q r : ℤ) (h : q + p = r)
      (a : (N.functor.obj ((OrdinarySchemeModuleFamilies.coefficientProjection X).obj l)).X.X p)
      (m : (E.toEnrichedFunctor.obj j).X q),
    HEq
      (((augmentation.app l).f r).hom
        (((eqToHom (B.value E l).symm).f r).hom
          ((E.toEnrichedFunctor.dgMap p (generator C f p (ULift.up a)) :
            Cochain _ _ p).v q r h m)))
      (ULift.up.{1} (moduleAction (raw.obj l).module (op PUnit.unit)
        (((N.functor.map (eqToHom (congrArg (fun F => F.obj l) base).symm)).hom.f p).hom a) h
        (((raw.map f).map.f q).hom
          ((((augmentation.app j).f q).hom ((eqToHom (B.value E j).symm).f q m)).down))))
  cocartesian : ∀ e : (nerve (Family X)) _⦋1⦌,
    IsCocartesianEdge M.projection ((nerveMap raw ≫ R.map).app (op ⦋1⦌) e)

/-- This source has its actual native DG section and its complete geometric augmentation. -/
structure AugmentedSection where
  object : CoefficientSection C
  cofibrant : IsCofibrantSection C object
  data : SmallGeometricAugmentation C M R B object

/-- Source morphisms are actual pairs of maps with the whole augmentation square. -/
structure AugmentedSectionMap (E F : AugmentedSection C M R B) where
  map : E.object ⟶ F.object
  raw : E.data.raw ⟶ F.data.raw
  base : Functor.whiskerRight raw (moduleProjection N) = eqToHom (E.data.base.trans F.data.base.symm)
  square : B.functor.map map ≫ F.data.augmentation = E.data.augmentation ≫
    Functor.whiskerRight (Functor.whiskerRight raw (DerivedSquareZeroFamilies.coefficientProjection N))
      (largeCochainLift ℤ)

def augmentedId (E : AugmentedSection C M R B) : AugmentedSectionMap C M R B E E where
  map := 𝟙 _
  raw := 𝟙 _
  base := by simp
  square := by ext j i; simp; exact (ModuleCat.id_apply _ _).symm

def augmentedComp {E F G : AugmentedSection C M R B}
    (a : AugmentedSectionMap C M R B E F) (b : AugmentedSectionMap C M R B F G) :
    AugmentedSectionMap C M R B E G where
  map := a.map ≫ b.map
  raw := a.raw ≫ b.raw
  base := by rw [Functor.whiskerRight_comp, a.base, b.base]; simp
  square := by
    rw [B.functor.map_comp, Category.assoc, b.square, ← Category.assoc, a.square]
    simp only [Functor.whiskerRight_comp, Category.assoc]

theorem augmentedMap_ext {E F : AugmentedSection C M R B} {a b : AugmentedSectionMap C M R B E F}
    (h : a.map = b.map) (g : a.raw = b.raw) : a = b := by
  cases a; cases b; cases h; cases g; rfl

instance : Category (AugmentedSection C M R B) where
  Hom := AugmentedSectionMap C M R B
  id := augmentedId C M R B
  comp := augmentedComp C M R B
  id_comp _ := augmentedMap_ext C M R B (Category.id_comp _) (Category.id_comp _)
  comp_id _ := augmentedMap_ext C M R B (Category.comp_id _) (Category.comp_id _)
  assoc _ _ _ := augmentedMap_ext C M R B (Category.assoc _ _ _) (Category.assoc _ _ _)

def augmentedRaw : AugmentedSection C M R B ⥤ (Family X ⥤ AffineModulePoint N) where
  obj E := E.data.raw
  map a := a.raw

/-- The original raw source at every joint augmentation/family parameter simplex. -/
def augmentedRawDegree (n m : SimplexCategoryᵒᵖ) (a : (nerve (AugmentedSection C M R B)).obj n)
    (g : n ⟶ m) (b : (nerve (Family X)).obj m) : (nerve (AffineModulePoint N)).obj m :=
  (a.whiskerLeft (SimplexCategory.toCat.map g.unop).toFunctor).prod' b ⋙
    Functor.uncurry.obj (augmentedRaw C M R B)

def IsGeometricCoefficient (E : CoefficientSection C) : Prop :=
  IsCofibrantSection C E ∧ Nonempty (SmallGeometricAugmentation C M R B E)

/-- The full native DG category preserves all homogeneous section transformations. -/
abbrev GeometricCoefficients :=
  letI := C.enrichment
  DGFullSubcategory (IsGeometricCoefficient C M R B)

instance : Category (GeometricCoefficients C M R B) where
  Hom E F := E.obj ⟶ F.obj
  id E := 𝟙 E.obj
  comp f g := f ≫ g
  id_comp f := Category.id_comp f
  comp_id f := Category.comp_id f
  assoc f g h := Category.assoc f g h

def geometricProjection : AugmentedSection C M R B ⥤ GeometricCoefficients C M R B where
  obj E := ⟨E.object, E.cofibrant, ⟨E.data⟩⟩
  map a := a.map

def geometricCycle {E F : GeometricCoefficients C M R B} (a : E ⟶ F) :
    letI := C.enrichment; dgCycles (LargeScalar ℤ) E F := by
  letI := C.enrichment
  let z := DGFunctor.homEquivDGCycles (LargeScalar ℤ) E.obj F.obj a
  have e : dgHomComplex (LargeScalar ℤ) E F = dgHomComplex (LargeScalar ℤ) E.obj F.obj :=
    DGFullSubcategory.dgHomComplex_eq (LargeScalar ℤ) E F
  let i := (eqToIso e).inv
  refine ⟨(i.f 0).hom z.val, ?_⟩
  rw [mem_dgCycles]
  have h := congrArg (fun f => f.hom z.val) (i.comm 0 1)
  have hz := (mem_dgCycles (LargeScalar ℤ)).mp z.property
  change (((dgHomComplex (LargeScalar ℤ) E F).d 0 1).hom) ((i.f 0).hom z.val) = 0
  change (((i.f 1).hom) ((dgDifferential (LargeScalar ℤ) 0) z.val)) =
    (((dgHomComplex (LargeScalar ℤ) E F).d 0 1).hom) ((i.f 0).hom z.val) at h
  rw [hz, map_zero] at h
  exact h.symm

def geometricNerve : SSet.{2} := by
  letI := C.enrichment
  exact dgNerve (k := LargeScalar ℤ) (GeometricCoefficients C M R B)

/-- Every actual closed source map is independently fixed by the native lax unit and cochain map. -/
structure GeometricClosedFunctor where
  functor : letI := C.enrichment
    GeometricCoefficients C M R B ⥤ DGSimplicial (k := LargeScalar ℤ) (GeometricCoefficients C M R B)
  object : letI := C.enrichment; ∀ E : GeometricCoefficients C M R B,
    functor.obj E = ForgetEnrichment.of SSet (DGSimplicialCategory.of (LargeScalar ℤ) E)
  map : letI := C.enrichment; ∀ (E F : GeometricCoefficients C M R B) (a : E ⟶ F),
    HEq (functor.map a) (simplicialArrow (geometricCycle C M R B a))

def augmentationNerve (F : GeometricClosedFunctor C M R B) :
    nerve (AugmentedSection C M R B) ⟶ geometricNerve C M R B := by
  letI := C.enrichment
  exact nerveMap (geometricProjection C M R B ⋙ F.functor) ≫
    SimplicialNerve.fromNerve (DGSimplicial (k := LargeScalar ℤ) (GeometricCoefficients C M R B))

def IsAugmentationWeak {E F : AugmentedSection C M R B} (a : E ⟶ F) : Prop :=
  ∀ j : Family X, QuasiIso ((B.functor.map a.map).app j)

def InvertsAugmentationWeak (Z : SSet.{2})
    (a : (mapping (nerve (AugmentedSection C M R B)) Z) _⦋0⦌) : Prop :=
  ∀ (E F : AugmentedSection C M R B) (f : E ⟶ F), IsAugmentationWeak C M R B f →
    IsEquivalenceEdge Z (((SimplicialCategory.homEquiv' _ _).symm a).app
      (op ⦋1⦌) (nerve.edgeMk f).edge)

/-- Full source localization includes the entire category of quasi-inverting functors. -/
structure CoefficientLocalization (F : GeometricClosedFunctor C M R B) where
  invert : ∀ (E G : AugmentedSection C M R B) (a : E ⟶ G), IsAugmentationWeak C M R B a →
    IsEquivalenceEdge (geometricNerve C M R B) ((augmentationNerve C M R B F).app
      (op ⦋1⦌) (nerve.edgeMk a).edge)
  universal : ∀ (Z : SSet.{2}) [SSet.Quasicategory Z],
    ∃ f : mapping (geometricNerve C M R B) Z ⟶
      ((mapping (nerve (AugmentedSection C M R B)) Z).fullEnhancedSubcategory
        (InvertsAugmentationWeak C M R B Z)).toSSet,
      f ≫ (SSet.Subcomplex.ι _) = precomposition (augmentationNerve C M R B F) Z ∧
        CategoricalWeakEquivalence f

/-- Raw realization is fixed on every joint source parameter and every original family simplex. -/
structure RawRealization where
  map : nerve (AugmentedSection C M R B) ⟶ liftSet.{1, 2} (OrdinarySchemeModuleFamilies.qcoh M X)
  normalized : ∀ (n m : SimplexCategoryᵒᵖ) (a : (nerve (AugmentedSection C M R B)).obj n)
    (g : n ⟶ m) (b : (nerve (Family X)).obj m),
    (((map.app n a).down.val.app m g) b) = R.map.app m (augmentedRawDegree C M R B n m a g b)

/-- One native equivalence of whole source functors fixes the full ordinary QCoh realization. -/
structure QCohRealization (F : GeometricClosedFunctor C M R B)
    (P : CoefficientLocalization C M R B F) (T : RawRealization C M R B) where
  map : geometricNerve C M R B ⟶ liftSet.{1, 2} (OrdinarySchemeModuleFamilies.qcoh M X)
  weak : CategoricalWeakEquivalence map
  comparison : SSet.Edge (X := mapping (nerve (AugmentedSection C M R B))
      (liftSet.{1, 2} (OrdinarySchemeModuleFamilies.qcoh M X)))
    ((SimplicialCategory.homEquiv' _ _) (augmentationNerve C M R B F ≫ map))
    ((SimplicialCategory.homEquiv' _ _) T.map)
  equivalence : IsEquivalenceEdge _ comparison.edge

variable {F : GeometricClosedFunctor C M R B} {P : CoefficientLocalization C M R B F}
  {T : RawRealization C M R B} (K : QCohRealization C M R B F P T)

/-- Perfectness is the same native finite-cell/retract test on every original constant-ring fibre. -/
def IsPerfectCoefficient (E : GeometricCoefficients C M R B) : Prop :=
  letI := C.enrichment
  OrdinarySchemeModuleFamilies.IsPerfectGlobal M X
    ((K.map.app (op ⦋0⦌) (objectVertex E)).down)

/-- The ordinary perfect DG category retains the full original section-cochain Hom in all degrees. -/
abbrev PerfectCoefficients :=
  letI := C.enrichment
  DGFullSubcategory (IsPerfectCoefficient C M R B K)

def perfectNerve : SSet.{2} := by
  letI := C.enrichment
  exact dgNerve (k := LargeScalar ℤ) (PerfectCoefficients C M R B K)

/-- The complete perfect comparison is fixed by the whole original QCoh realization. -/
structure PerfectComparison where
  map : perfectNerve C M R B K ⟶ liftSet.{1, 2} (OrdinarySchemeModuleFamilies.perf M X)
  normalized : letI := C.enrichment
    map ≫ liftSetMap
      (((OrdinarySchemeModuleFamilies.qcoh M X).fullEnhancedSubcategory
        (OrdinarySchemeModuleFamilies.IsPerfectGlobal M X)).ι) =
      dgNerveMap (DGFullSubcategory.inclusion (R := LargeScalar ℤ)
        (P := IsPerfectCoefficient C M R B K)) ≫ K.map

end MathlibExt.AlgebraicGeometry.OrdinaryFamilyCoefficientModels
