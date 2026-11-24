/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
public import MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
public import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Full QCoh enhancements and actual global Hom complexes

The coefficient ring is canonically lifted to the universe of the
entire affine-family category. The native DG nerve is compared with
the actual category of cocartesian module sections, retaining all
arrows. A structure-sheaf section is pulled back from the same regular
unit system over all simplicial algebras; it is not chosen separately
on an atlas of X.

Global sections are the literal enriched Hom from this structure
sheaf. Restriction of its representable module along the normalized
coefficient functor retains the full coefficient action. Source model
data do not assert compactness, duality, orientations or nondegeneracy.

References: PTVV arXiv:1111.3209v4, §2.1, Definition 2.1;
Toën--Vezzosi, HAG II, Part 2; Lurie, Higher Algebra, §7.3.
Native DG operations and their Apache notices remain in DGSource.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open scoped Simplicial

universe u v w
variable {k : Type u} [CommRing k]

/-- The canonical coefficient ring in the universe of all affine families. -/
abbrev LargeScalar (k : Type u) := ULift.{u + 1} k

/-- Cochains are lifted termwise and retain the literal transported scalar action. -/
def largeCochainLift (k : Type u) [CommRing k] :
    Cochains k ⥤ Cochains (LargeScalar k) :=
  liftComplex k ⋙
    (ModuleCat.restrictScalars
      (ULift.ringEquiv : LargeScalar k ≃+* k).toRingHom).mapHomologicalComplex (.up ℤ)

/-- A coefficient lift uses the actual pure-tensor formula in every total degree. -/
structure CochainLiftModel (k : Type u) [CommRing k] where
  [monoidal : (largeCochainLift k).LaxMonoidal]
  tensor_normalized : ∀ (C D : Cochains k) (p q n : ℤ) (h : p + q = n)
    (a : C.X p) (b : D.X q),
    ((HomologicalComplex.ιTensorObj ((largeCochainLift k).obj C)
        ((largeCochainLift k).obj D) p q n h) ≫
      ((Functor.LaxMonoidal.μ (largeCochainLift k) C D).f n)).hom
        (TensorProduct.tmul (LargeScalar k) (ULift.up a) (ULift.up b)) =
      ULift.up ((HomologicalComplex.ιTensorObj C D p q n h).hom
        (TensorProduct.tmul k a b))
  unit_normalized : ∀ a : k,
    ((Functor.LaxMonoidal.ε (largeCochainLift k)).f 0).hom (ULift.up a) = ULift.up a

/-- Object lifting retains the original small DG Hom/identity/composition on the nose. -/
@[instance_reducible]
def smallLiftEnrichment (C : Type v) [DGCategory k C] :
    DGCategory k (ULift.{u + 1} C) where
  Hom X Y := dgHomComplex k X.down Y.down
  id X := eId (Cochains k) X.down
  comp X Y Z := eComp (Cochains k) X.down Y.down Z.down
  id_comp X Y := EnrichedCategory.id_comp (V := Cochains k) X.down Y.down
  comp_id X Y := EnrichedCategory.comp_id (V := Cochains k) X.down Y.down
  assoc X Y Z W := EnrichedCategory.assoc (V := Cochains k)
    X.down Y.down Z.down W.down

/-- Change only the source universe and enrichment, through the fixed coefficient lift. -/
@[reducible]
def liftedDGCategory (L : CochainLiftModel k) (C : Type u) [DGCategory k C] :
    DGCat (LargeScalar k) := by
  letI := L.monoidal
  letI := smallLiftEnrichment (k := k) C
  exact DGCat.of (LargeScalar k) (TransportEnrichment (largeCochainLift k) (ULift.{u + 1} C))

/-- Native vertices of a DG category in arbitrary object/coefficient universes. -/
def objectVertex {R : Type v} [CommRing R] {C : Type w} [DGCategory R C] (x : C) :
    (dgNerve (k := R) C) _⦋0⦌ :=
  (SimplicialNerve.vertexEquiv (DGSimplicial (k := R) C)).symm
    (ForgetEnrichment.of SSet (DGSimplicialCategory.of R x))

/-- A possibly large DG category whose original coefficient Hom complexes are small. -/
structure LocallySmallDG (k : Type u) [CommRing k] where
  carrier : Type (u + 1)
  [enrichment : DGCategory k carrier]

attribute [instance] LocallySmallDG.enrichment
instance : CoeSort (LocallySmallDG k) (Type (u + 1)) := ⟨LocallySmallDG.carrier⟩

instance : Category (LocallySmallDG k) where
  Hom C D := EnrichedFunctor (Cochains k) C D
  id C := EnrichedFunctor.id (Cochains k) C
  comp F G := F.comp (Cochains k) G
  id_comp F := by cases F; rfl
  comp_id F := by cases F; rfl
  assoc F G H := by cases F; cases G; cases H; rfl

/-- The larger coefficient enrichment is the fixed lift on all original Hom complexes. -/
@[reducible]
def liftLocallySmall (L : CochainLiftModel k) (C : LocallySmallDG k) :
    DGCat (LargeScalar k) := by
  letI := L.monoidal
  letI := smallLiftEnrichment (k := k) C
  exact DGCat.of (LargeScalar k)
    (TransportEnrichment (largeCochainLift k) (ULift.{u + 1} C))

/-- Lift an actual DG functor without changing any original homogeneous Hom map. -/
def liftLocallySmallMap (L : CochainLiftModel k) {C D : LocallySmallDG k} (F : C ⟶ D) :
    liftLocallySmall L C ⟶ liftLocallySmall L D := by
  letI := L.monoidal
  letI := smallLiftEnrichment (k := k) C
  letI := smallLiftEnrichment (k := k) D
  let G : EnrichedFunctor (Cochains k) (ULift.{u + 1} C) (ULift.{u + 1} D) :=
    { obj X := ULift.up (F.obj X.down)
      map X Y := F.map X.down Y.down
      map_id X := F.map_id X.down
      map_comp X Y Z := F.map_comp X.down Y.down Z.down }
  exact transportFunctor (C := ULift.{u + 1} C) (D := ULift.{u + 1} D)
    (V := Cochains k) (W := Cochains (LargeScalar k)) (largeCochainLift k) G

/-- A source universe comparison is a natural iso on the entire DG-category
functor, not separate choices on geometric affine charts. -/
structure NerveLiftModel (L : CochainLiftModel k) where
  comparison : ∀ C : LocallySmallDG k,
    dgNerve (k := LargeScalar k) (liftLocallySmall L C) ≅ dgNerve (k := k) C
  natural : ∀ (C D : LocallySmallDG k) (F : C ⟶ D),
    dgNerveMap (liftLocallySmallMap L F) ≫ (comparison D).hom =
      (comparison C).hom ≫ dgNerveMap F
  vertex : ∀ (C : LocallySmallDG k) (x : C),
    (comparison C).hom.app (op ⦋0⦌) (objectVertex (ULift.up x : liftLocallySmall L C)) =
      objectVertex x

/-- The literal original coefficient DG category in the full sized source category. -/
@[reducible]
def coefficientSource (N : ShuffleAlgebraFunctor k) (A : SAlg k) : LocallySmallDG k := by
  letI := smallLiftEnrichment (k := k) (coefficientCategory N A)
  exact ⟨ULift.{u + 1} (coefficientCategory N A)⟩

instance coefficientSource_enrichment (N : ShuffleAlgebraFunctor k) (A : SAlg k) :
    DGCategory k (coefficientSource N A) := (coefficientSource N A).enrichment

/-- The actual large coefficient category has the lifted normalization N(A), with its action. -/
abbrev coefficientLarge (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k) (A : SAlg k) :=
  liftLocallySmall L (coefficientSource N A)

/-- The native coefficient object is the same lifted regular unit in every algebra. -/
def coefficientObject (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k) (A : SAlg k) :
    coefficientLarge L N A := ULift.up (ULift.up PUnit.unit)

/-- Coefficient arrows retain their actual normalized algebra map before the universe lift. -/
def coefficientSourceMap (N : ShuffleAlgebraFunctor k) {A B : SAlg k} (f : A ⟶ B) :
    coefficientSource N A ⟶ coefficientSource N B where
  obj x := ULift.up ((coefficientMap N f).obj x.down)
  map x y := (coefficientMap N f).map x.down y.down
  map_id x := (coefficientMap N f).map_id x.down
  map_comp x y z := (coefficientMap N f).map_comp x.down y.down z.down

/-- The large coefficient map is the same source map in every cochain degree. -/
def coefficientLargeMap (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k)
    {A B : SAlg k} (f : A ⟶ B) : coefficientLarge L N A ⟶ coefficientLarge L N B :=
  liftLocallySmallMap L (coefficientSourceMap N f)

/-- Its scalar-complex map has exactly the same native coefficient source and target. -/
def coefficientCochainMap (L : CochainLiftModel k) (N : ShuffleAlgebraFunctor k)
    {A B : SAlg k} (f : A ⟶ B) :
    dgHomComplex (LargeScalar k) (coefficientObject L N A) (coefficientObject L N A) ⟶
      dgHomComplex (LargeScalar k) (coefficientObject L N B) (coefficientObject L N B) :=
  (coefficientLargeMap L N f).map (coefficientObject L N A) (coefficientObject L N A)

variable {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    (M : AffineModuleFibration N S)

/-- The regular coefficient unit, with its actual representable DG action. -/
def regularUnit (A : SAlg k) : RightModule k (coefficientCategory N A) :=
  (dgYoneda k (C := coefficientCategory N A)).obj PUnit.unit

/-- The unit system is a full cocartesian section over all algebras.
Its local values are the actual regular modules, not unrelated lines. -/
structure RegularUnitSystem where
  cofibrant : ∀ A : SAlg k, IsCofibrantModule (regularUnit (N := N) A)
  map : nerve (SAlg k) ⟶ M.total
  projection : map ≫ M.projection = 𝟙 _
  value : ∀ A : SAlg k,
    map.app (op ⦋0⦌) (ComposableArrows.mk₀ A) =
      ((M.realization A) ≫ pullback.fst M.projection (algebraPoint A)).app (op ⦋0⦌)
        (objectVertex (⟨regularUnit (N := N) A, cofibrant A⟩ :
          DGDerivedModules k (coefficientCategory N A)))
  cocartesian : ∀ e : (nerve (SAlg k)) _⦋1⦌,
    IsCocartesianEdge M.projection (map.app (op ⦋1⦌) e)

/-- The actual global structure section is the pullback of this one unit system. -/
def structureSection (U : RegularUnitSystem M) (X : Prestack k) : (qcoh M X) _⦋0⦌ := by
  let f := nerveMap (algebraProjection X) ≫ U.map
  refine ⟨Functor.HomObj.ofNatTrans f, ?_, ?_⟩
  · intro n g x
    change M.projection.app n (f.app n x) = (nerveMap (algebraProjection X)).app n x
    have h : f ≫ M.projection = nerveMap (algebraProjection X) := by
      dsimp only [f]
      rw [Category.assoc, U.projection, Category.comp_id]
    exact congrArg (fun t => t.app n x) h
  · intro i e
    exact U.cocartesian ((nerveMap (algebraProjection X)).app (op ⦋1⦌) e)

/-- The actual affine augmentation family, rather than a selected closed point. -/
def affineAugmentationFamily (Q : AlgebraReplacementFunctor k) (A : SAlg k) :
    Families (affineMapping k Q A) :=
  family (affineMapping k Q A) A (op ⦋0⦌) (ULift.up (affineAugmentationSimplex Q A (op ⦋0⦌)))

/-- The source-covered affine QCoh comparison is the inverse of native
evaluation at the actual augmentation, on the complete category. -/
structure AffineQCohNormalization (U : RegularUnitSystem M) (Q : AlgebraReplacementFunctor k)
    (A : SAlg k) where
  inverse : moduleFibre M.projection A ⟶ qcoh M (affineMapping k Q A)
  evaluation_weak : CategoricalWeakEquivalence
    (evaluationFibre M (affineMapping k Q A) (affineAugmentationFamily Q A))
  normalized : (categoricalQ.{u}).map inverse ≫
    (categoricalQ.{u}).map
      (evaluationFibre M (affineMapping k Q A) (affineAugmentationFamily Q A)) = 𝟙 _
  unit_value : inverse.app (op ⦋0⦌)
      ((M.realization A).app (op ⦋0⦌)
        (objectVertex (⟨regularUnit (N := N) A, U.cofibrant A⟩ :
          DGDerivedModules k (coefficientCategory N A)))) =
    structureSection M U (affineMapping k Q A)

/-- Regular coefficient Yoneda into cofibrant modules keeps all scalar Hom degrees. -/
def regularYoneda (U : RegularUnitSystem M) (A : SAlg k) :
    coefficientSource N A ⟶ (⟨DGDerivedModules k (coefficientCategory N A)⟩ : LocallySmallDG k) where
  obj x := ⟨(dgYoneda k (C := coefficientCategory N A)).obj x.down, by
    cases x with
    | up x =>
      cases x
      exact U.cofibrant A⟩
  map x y := (dgYoneda k (C := coefficientCategory N A)).map x.down y.down
  map_id x := (dgYoneda k (C := coefficientCategory N A)).map_id x.down
  map_comp x y z := (dgYoneda k (C := coefficientCategory N A)).map_comp x.down y.down z.down

/-- The affine scalar unit map is assembled from original Yoneda, native
evaluation and one globally natural universe comparison. -/
def affineScalarReference (U : RegularUnitSystem M) (Q : AlgebraReplacementFunctor k)
    (L : CochainLiftModel k) (V : NerveLiftModel L) (A : SAlg k)
    (B : AffineQCohNormalization M U Q A) :
    dgNerve (k := LargeScalar k) (coefficientLarge L N A) ⟶ qcoh M (affineMapping k Q A) :=
  (V.comparison (coefficientSource N A)).hom ≫
    dgNerveMap (regularYoneda M U A) ≫ M.realization A ≫ B.inverse

/-- A full global DG realization of the native QCoh category and its structure section. -/
structure QCohEnhancement (U : RegularUnitSystem M) (X : Prestack k) where
  category : DGCat (LargeScalar k)
  realization : dgNerve (k := LargeScalar k) category ⟶ qcoh M X
  weak : CategoricalWeakEquivalence realization
  unit : category
  unit_value : realization.app (op ⦋0⦌) (objectVertex unit) = structureSection M U X

variable {M}

/-- Global Hom is the actual enriched RHom(O_X,E) of this full enhancement. -/
def globalHom {U : RegularUnitSystem M} {X : Prestack k}
    (G : QCohEnhancement M U X) (E : G.category) : Cochains (LargeScalar k) :=
  dgHomComplex (LargeScalar k) G.unit E

/-- Actual perfection is tested on the same full QCoh section, in every affine family. -/
def IsPerfect {U : RegularUnitSystem M} {X : Prestack k}
    (G : QCohEnhancement M U X) (E : G.category) : Prop :=
  IsPerfectGlobal M X (G.realization.app (op ⦋0⦌) (objectVertex E))

/-- A coefficient functor represents scalar action on the same global structure section. -/
structure CoefficientRealization {U : RegularUnitSystem M} {X : Prestack k}
    (G : QCohEnhancement M U X) (L : CochainLiftModel k) (A : SAlg k)
    (Q : AlgebraReplacementFunctor k) (b : X ⟶ affineMapping k Q A)
    (V : NerveLiftModel L) (B : AffineQCohNormalization M U Q A) where
  functor : coefficientLarge L N A ⟶ G.category
  unit_value : functor.obj (ULift.up (ULift.up PUnit.unit)) = G.unit
  normalized : (categoricalQ.{u}).map (dgNerveMap functor ≫ G.realization) =
    (categoricalQ.{u}).map
      (affineScalarReference M U Q L V A B ≫ qcohPullback M b)

/-- A source coefficient/QCoh enhancement is chosen together with its complete scalar realization. -/
structure CoefficientQCohEnhancement (M : AffineModuleFibration N S) (U : RegularUnitSystem M)
    (Q : AlgebraReplacementFunctor k) (L : CochainLiftModel k) (V : NerveLiftModel L)
    (A : SAlg k) (B : AffineQCohNormalization M U Q A)
    (X : Prestack k) (b : X ⟶ affineMapping k Q A) where
  model : QCohEnhancement M U X
  scalar : CoefficientRealization model L A Q b V B

/-- RΓ with its full A-coefficient action is a restricted actual representable module. -/
def globalModule {U : RegularUnitSystem M} {X : Prestack k}
    {G : QCohEnhancement M U X} {L : CochainLiftModel k} {A : SAlg k}
    {Q : AlgebraReplacementFunctor k} {b : X ⟶ affineMapping k Q A}
    {V : NerveLiftModel L} {B : AffineQCohNormalization M U Q A}
    (I : CoefficientRealization G L A Q b V B) (E : G.category) :
    RightModule (LargeScalar k) (coefficientLarge L N A) :=
  ⟨(EnrichedFunctor.op (V := Cochains (LargeScalar k)) I.functor).comp
    (Cochains (LargeScalar k)) (dgRepresentable (LargeScalar k) E)⟩

end MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
