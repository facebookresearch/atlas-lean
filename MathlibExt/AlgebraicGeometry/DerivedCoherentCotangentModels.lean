/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedGlobalCotangentModels
public import MathlibExt.AlgebraicTopology.SimplicialCovariantModels
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-!
# Coherent cotangent representation over every actual coefficient test

The test category is the actual split square-zero family category,
restricted to its genuine coherent kernels. The kernel diagram is fixed
on every joint test/family simplex by the raw semilinear functor.
Its DG realization is compared by an actual natural equivalence of
whole functors. Derivations are the native iterated limit of a replacement
of the complete joint coefficient/family fibre diagram.

Cotangent corepresentability is a fibrewise weak equivalence of the
actual left mapping fibration and actual derivation left fibration over
this one test category. The base-preserving map retains every higher
module naturality simplex, not only equalities in a homotopy category.

References: HAG II math/0404373v7 §§1.3.7 and 1.4.1; PTVV1111.3209v4 conventions and §1.2;
Lurie HTT §§2.1--2.2 and Higher Algebra §7.3.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.HomotopicalAlgebra
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicTopology.QuasicategoricalModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedFamilyDerivations
open MathlibExt.AlgebraicGeometry.DerivedGlobalCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k]

/-- The complete kernel functor, normalized on all square-zero system maps. -/
structure KernelSystem (N : ShuffleAlgebraFunctor k) (X : Prestack k) where
  functor : SquareZeroFamily X ⥤ (Families X ⥤ AffineModulePoint N)
  model : ∀ E : SquareZeroFamily X, KernelFamily N E
  object_eq : ∀ E : SquareZeroFamily X, functor.obj E = (model E).functor
  map_model : ∀ (E F : SquareZeroFamily X) (f : E ⟶ F),
    KernelFamilyMap (model E) (model F) f
  map_eq : ∀ (E F : SquareZeroFamily X) (f : E ⟶ F),
    HEq (functor.map f) (map_model E F f).map
  base_eq : ∀ E : SquareZeroFamily X,
    (model E).functor ⋙ moduleProjection N = algebraProjection X

variable {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
variable (M : AffineModuleFibration N S) (R : RawModuleRealization M)
variable {X : Prestack k} (K : KernelSystem N X)

/-- A coefficient test has the actual cocartesian kernel transports. -/
def IsCoherentKernel (E : SquareZeroFamily X) : Prop :=
  ∀ e : (nerve (Families X)) _⦋1⦌,
    IsCocartesianEdge M.projection
      ((nerveMap (K.model E).functor ≫ R.map).app (op ⦋1⦌) e)

/-- The genuine category of coherent first-order coefficient tests. -/
abbrev CoefficientTest :=
  ObjectProperty.FullSubcategory (IsCoherentKernel M R K)

/-- Every test retains its actual split square-zero system. -/
def testInclusion : CoefficientTest M R K ⥤ SquareZeroFamily X :=
  ObjectProperty.ι (IsCoherentKernel M R K)

/-- The actual raw kernel diagram on the whole test category. -/
def rawKernels : CoefficientTest M R K ⥤ (Families X ⥤ AffineModulePoint N) :=
  testInclusion M R K ⋙ K.functor

/-- Every joint test/family simplex is evaluated by the actual uncurried kernel functor. -/
def rawKernelDegree (n m : SimplexCategoryᵒᵖ)
    (a : (nerve (CoefficientTest M R K)).obj n) (b : (nerve (Families X)).obj m)
    (g : n ⟶ m) : (nerve (AffineModulePoint N)).obj m :=
  (a.whiskerLeft (SimplexCategory.toCat.map g.unop).toFunctor).prod' b ⋙
    Functor.uncurry.obj (rawKernels M R K)

/-- Full realization is fixed on all joint simplices, not independent fibre objects. -/
structure KernelSectionFunctor where
  map : nerve (CoefficientTest M R K) ⟶ qcoh M X
  normalized : ∀ (n m : SimplexCategoryᵒᵖ)
    (a : (nerve (CoefficientTest M R K)).obj n) (g : n ⟶ m)
    (b : (nerve (Families X)).obj m),
    (((map.app n a).val.app m g) b) = R.map.app m (rawKernelDegree M R K n m a b g)

variable {U : RegularUnitSystem M} (G : QCohEnhancement M U X)

/-- The whole DG kernel functor has an actual coherent natural equivalence
to the full source kernel-section functor. -/
structure KernelDGFunctor (F : KernelSectionFunctor M R K) where
  map : nerve (CoefficientTest M R K) ⟶ dgNerve (k := LargeScalar k) G.category
  comparison : SSet.Edge
    (X := SimplicialDerivedModels.mapping (nerve (CoefficientTest M R K)) (qcoh M X))
    ((SimplicialCategory.homEquiv' _ _) (map ≫ G.realization))
    ((SimplicialCategory.homEquiv' _ _) F.map)
  equivalence : IsEquivalenceEdge
    (SimplicialDerivedModels.mapping (nerve (CoefficientTest M R K)) (qcoh M X)) comparison.edge

/-- The actual algebra diagram over the product of all tests and all affine-family simplices. -/
def jointAlgebras : CoefficientTest M R K × Families X ⥤ SAlg k :=
  Functor.uncurry.obj (testInclusion M R K ⋙ squareAlgebraFunctor X)

/-- Actual standard-simplex parameters in the whole joint diagram. -/
def jointSimplexes : (CoefficientTest M R K × Families X)ᵒᵖ ⥤ SSet.{u + 1} :=
  (CategoryTheory.Prod.snd (CoefficientTest M R K) (Families X)).op ⋙ simplexFamilies X

/-- Native mapping retains both coefficient-test and family-simplex directions. -/
def jointMapping (F : CoefficientTest M R K × Families X ⥤ SSet.{u + 1}) :
    CoefficientTest M R K × Families X ⥤ SSet.{u + 1} :=
  (((opOpEquivalence (CoefficientTest M R K × Families X)).inverse ⋙
      (jointSimplexes M R K).op).prod' F) ⋙
    Functor.uncurry.obj (SimplicialCategory.sHomFunctor SSet.{u + 1})

/-- The complete actual lift-mapping diagram X(E). -/
def jointLifts : CoefficientTest M R K × Families X ⥤ SSet.{u + 1} :=
  jointMapping M R K (jointAlgebras M R K ⋙ X)

/-- The actual tautological family-mapping diagram X(A). -/
def jointBase : CoefficientTest M R K × Families X ⥤ SSet.{u + 1} :=
  jointMapping M R K (CategoryTheory.Prod.snd _ _ ⋙ algebraProjection X ⋙ X)

/-- Assembly of the actual projection and tautological simplex, with every value fixed. -/
structure JointLiftProjection where
  map : jointLifts M R K ⟶ jointBase M R K
  projection : ∀ (t : CoefficientTest M R K) (j : Families X),
    HEq (map.app (t,j)) ((liftProjection X ((testInclusion M R K).obj t)).app j)
  point : (Functor.const (CoefficientTest M R K × Families X)).obj
    (Δ[0] : SSet.{u + 1}) ⟶ jointBase M R K
  point_eq : ∀ (t : CoefficientTest M R K) (j : Families X),
    HEq (point.app (t,j)) ((familyPoint X).app j)

/-- A true natural path model of this exact joint base diagram. -/
structure JointPath extends PrepathObject (jointBase M R K) where
  kan : ∀ j, SSet.KanComplex ((jointBase M R K).obj j)
  diagonal_weak : ∀ j, WeakEquivalence (ι.app j)
  endpoints_fibration : ∀ j,
    SSet.modelCategoryQuillen.J.rlp (prod.lift (p₀.app j) (p₁.app j))

/-- The actual joint diagram of all first-order compatible lifts. -/
def jointDerivations (P : JointLiftProjection M R K) (B : JointPath M R K) :
    CoefficientTest M R K × Families X ⥤ SSet.{u + 1} :=
  pullback (prod.map P.map P.point) (prod.lift B.p₀ B.p₁)

/-- Replacement is on the entire joint diagram, preserving every test morphism. -/
structure JointDerivationModel (P : JointLiftProjection M R K) (B : JointPath M R K) where
  replacement : SpaceDiagramReplacement.{u, u + 1, u + 1} (jointDerivations M R K P B)

/-- The true derived derivation functor uses native limits in the family direction. -/
def derivationFunctor {P : JointLiftProjection M R K} {B : JointPath M R K}
    (D : JointDerivationModel M R K P B) : CoefficientTest M R K ⥤ SSet.{u + 1} :=
  Functor.curry.obj D.replacement.diagram ⋙ lim

/-- The actual raw simplex-element total space of the derivation functor. -/
def rawDerivationTotal {P : JointLiftProjection M R K} {B : JointPath M R K}
    (D : JointDerivationModel M R K P B) : SSet.{u + 1} :=
  nerve ((Functor.uncurry.obj (derivationFunctor M R K D)).Elements)

/-- Its literal projection to the coefficient test, including all simplex morphisms. -/
def rawDerivationProjection {P : JointLiftProjection M R K} {B : JointPath M R K}
    (D : JointDerivationModel M R K P B) :
    rawDerivationTotal M R K D ⟶ nerve (CoefficientTest M R K) :=
  nerveMap (Functor.Elements.π (Functor.uncurry.obj (derivationFunctor M R K D)) ⋙
    CategoryTheory.Prod.fst _ _)

/-- The actual derived-space unstraightening is a covariant replacement of that full total. -/
abbrev DerivationFibration {P : JointLiftProjection M R K} {B : JointPath M R K}
    (D : JointDerivationModel M R K P B) :=
  CovariantReplacement (rawDerivationProjection M R K D)

variable {M R K G}

/-- The actual left Hom fibration pulled back by the whole source kernel functor. -/
def homFamily {F : KernelSectionFunctor M R K} (KG : KernelDGFunctor M R K G F)
    (L : G.category) : SSet.{u + 1} :=
  pullback (targetProjection (dgNerve (k := LargeScalar k) G.category) (objectVertex L)) KG.map

/-- The actual coefficient-test projection of that mapping fibration. -/
def homFamilyProjection {F : KernelSectionFunctor M R K} (KG : KernelDGFunctor M R K G F)
    (L : G.category) : homFamily KG L ⟶ nerve (CoefficientTest M R K) := pullback.snd _ _

/-- A coherent cotangent represents the entire derived coefficient functor.
The one map over the test base retains all higher naturality data. -/
structure CoherentGlobalCotangent {F : KernelSectionFunctor M R K}
    (KG : KernelDGFunctor M R K G F) {P : JointLiftProjection M R K} {B : JointPath M R K}
    (D : JointDerivationModel M R K P B) (DF : DerivationFibration M R K D) where
  object : G.category
  map : homFamily KG object ⟶ DF.total
  over : map ≫ DF.projection = homFamilyProjection KG object
  weak : ∀ t : CoefficientTest M R K,
    WeakEquivalence (fibreMap (homFamilyProjection KG object) DF.projection map over
      (ComposableArrows.mk₀ t))

end MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels
