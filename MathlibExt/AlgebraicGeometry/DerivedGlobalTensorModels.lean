/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
public import MathlibExt.AlgebraicGeometry.JointCoherentTensorFrames
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic

/-!
# Full module tensor fibrations and global perfect duals

The affine tensor functors have the actual balanced coequalizer modules
and homogeneous quotient-map formulas. A tensor fibration retains the
entire categorical nerve of these functors, over all algebras. Global
tensor simplices are fixed by their complete parameterized section maps,
rather than by unrelated affine object identifications.

A global DG/monoidal enhancement realizes that same full tensor map.
Perfect duals use the native exact-pairing triangle identities for this
tensor and the actual structure unit. Global section pairings are then
computed by enriched tensor, native unitors, and actual evaluation.

References: PTVV arXiv:1111.3209v4, §2.1, Remark 2.2 and Definition 2.4;
Lurie, Higher Algebra, §7.3. Construction providers remain separate.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory _root_.CategoryTheory.MonoidalClosed
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.SimplicialDerivedModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.AlgebraicTopology.CategoricalCocartesianSections
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.JointCoherentTensorFrames
open scoped Simplicial

universe u v

variable {R : Type u} [CommRing R] {C : Type v} [DGCategory R C]

/-- Fixing the first tensor factor keeps the complete native homogeneous DG map. -/
structure FixedLeftModel (T : EnrichedFunctor (Cochains R) (C × C) C) (x : C) where
  functor : EnrichedFunctor (Cochains R) C C
  object_eq : ∀ y : C, functor.obj y = T.obj (x, y)
  map_eq : ∀ (y z : C) (n : ℤ) (f : DGHom R n y z),
    HEq (functor.dgMap n f)
      (T.dgMap n (dgTensorHom R (C := C) (D := C) (X := (x, y)) (Y := (x, z))
        (p := 0) (q := n) (n := n) (dgId R x) f (zero_add n)))

/-- Fixing the second tensor factor keeps the complete native homogeneous DG map. -/
structure FixedRightModel (T : EnrichedFunctor (Cochains R) (C × C) C) (y : C) where
  functor : EnrichedFunctor (Cochains R) C C
  object_eq : ∀ x : C, functor.obj x = T.obj (x, y)
  map_eq : ∀ (x z : C) (n : ℤ) (f : DGHom R n x z),
    HEq (functor.dgMap n f)
      (T.dgMap n (dgTensorHom R (C := C) (D := C) (X := (x, y)) (Y := (z, y))
        (p := n) (q := 0) (n := n) f (dgId R y) (add_zero n)))

/-- The actual constant-first-factor map on every coherent nerve simplex. -/
def constantLeft (x : C) : dgNerve (k := R) C ⟶ dgNerve (k := R) C ⊗ dgNerve (k := R) C :=
  (λ_ _).inv ≫ (SSet.const (objectVertex x) ⊗ₘ 𝟙 _)

/-- The actual constant-second-factor map on every coherent nerve simplex. -/
def constantRight (y : C) : dgNerve (k := R) C ⟶ dgNerve (k := R) C ⊗ dgNerve (k := R) C :=
  (ρ_ _).inv ≫ (𝟙 _ ⊗ₘ SSet.const (objectVertex y))

/-- A tensor nerve fixes every joint coherent-frame coefficient. -/
structure NerveTensorModel (T : EnrichedFunctor (Cochains R) (C × C) C) where
  map : dgNerve (k := R) C ⊗ dgNerve (k := R) C ⟶ dgNerve (k := R) C
  vertex : ∀ x y : C,
    map.app (op ⦋0⦌) (objectVertex x, objectVertex y) = objectVertex (T.obj (x, y))
  joint : ∀ (n : SimplexCategoryᵒᵖ) (a b : (dgNerve (k := R) C).obj n),
    JointFrameModel T a b (map.app n (a, b))
  fixedLeft : ∀ x : C, FixedLeftModel T x
  fixedRight : ∀ y : C, FixedRightModel T y
  left : ∀ x : C, constantLeft x ≫ map = dgNerveMap (fixedLeft x).functor
  right : ∀ y : C, constantRight y ≫ map = dgNerveMap (fixedRight y).functor

variable {k : Type u} [CommRing k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} (M : AffineModuleFibration N S)

/-- The actual first projection of a simplicial product. -/
def tensorLeftProjection (A B : SSet.{v}) : A ⊗ B ⟶ A where
  app _n := ↾fun x => x.1
  naturality _ _ _ := rfl

/-- The actual second projection of a simplicial product. -/
def tensorRightProjection (A B : SSet.{v}) : A ⊗ B ⟶ B where
  app _n := ↾fun x => x.2
  naturality _ _ _ := rfl

/-- An actual tensor fibration is fixed by the complete affine derived tensors. -/
structure TensorFibrationModel where
  affine : ∀ A : SAlg k, DerivedTensorModel (coefficientCategory N A) PUnit.unit
  nerve : ∀ A : SAlg k, NerveTensorModel (affine A).functor
  map : pullback M.projection M.projection ⟶ M.total
  over : map ≫ M.projection = pullback.fst M.projection M.projection ≫ M.projection
  pair : ∀ A : SAlg k,
    dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A)) ⊗
      dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A)) ⟶
        pullback M.projection M.projection
  pair_fst : ∀ A : SAlg k,
    pair A ≫ pullback.fst M.projection M.projection =
      (tensorLeftProjection _ _) ≫ M.realization A ≫
        pullback.fst M.projection (algebraPoint A)
  pair_snd : ∀ A : SAlg k,
    pair A ≫ pullback.snd M.projection M.projection =
      (tensorRightProjection _ _) ≫ M.realization A ≫
        pullback.fst M.projection (algebraPoint A)
  normalized : ∀ A : SAlg k,
    pair A ≫ map = (nerve A).map ≫ M.realization A ≫
      pullback.fst M.projection (algebraPoint A)
  cocartesian : ∀ e : (pullback M.projection M.projection) _⦋1⦌,
    IsCocartesianEdge M.projection ((pullback.fst M.projection M.projection).app (op ⦋1⦌) e) →
    IsCocartesianEdge M.projection ((pullback.snd M.projection M.projection).app (op ⦋1⦌) e) →
    IsCocartesianEdge M.projection (map.app (op ⦋1⦌) e)

/-- A mapping simplex is evaluated by the native internal-Hom counit on its whole parameter. -/
def parameterEvaluation {A E : SSet.{u + 1}} {n : SimplexCategoryᵒᵖ}
    (a : (SimplicialDerivedModels.mapping A E).obj n) : A ⊗ SSet.stdSimplex.obj n.unop ⟶ E :=
  (𝟙 A ⊗ₘ SSet.yonedaEquiv.symm a) ≫ (ihom.ev A).app E

/-- Tensoring global sections fixes the full parameter/affine-family map. -/
structure TensorSectionModel (T : TensorFibrationModel M) (X : Prestack k) where
  map : qcoh M X ⊗ qcoh M X ⟶ qcoh M X
  pair : ∀ (n : SimplexCategoryᵒᵖ) (_a _b : (qcoh M X).obj n),
    nerve (Families X) ⊗ SSet.stdSimplex.obj n.unop ⟶ pullback M.projection M.projection
  pair_fst : ∀ (n : SimplexCategoryᵒᵖ) (a b : (qcoh M X).obj n),
    pair n a b ≫ pullback.fst M.projection M.projection = parameterEvaluation a.val
  pair_snd : ∀ (n : SimplexCategoryᵒᵖ) (a b : (qcoh M X).obj n),
    pair n a b ≫ pullback.snd M.projection M.projection = parameterEvaluation b.val
  normalized : ∀ (n : SimplexCategoryᵒᵖ) (a b : (qcoh M X).obj n),
    parameterEvaluation ((map.app n (a, b)).val) = pair n a b ≫ T.map

variable {M}

/-- The native category of closed morphisms in the full global enhancement. -/
abbrev Closed {U : RegularUnitSystem M} {X : Prestack k} (G : QCohEnhancement M U X) :=
  ForgetEnrichment (Cochains (LargeScalar k)) G.category

/-- Global tensor/monoidal data realize exactly the same full source section tensor. -/
structure MonoidalEnhancement {U : RegularUnitSystem M} {X : Prestack k}
    (G : QCohEnhancement M U X) {T : TensorFibrationModel M} (F : TensorSectionModel M T X) where
  tensor : EnrichedFunctor (Cochains (LargeScalar k)) (G.category × G.category) G.category
  nerve : NerveTensorModel tensor
  realization : nerve.map ≫ G.realization = (G.realization ⊗ₘ G.realization) ≫ F.map
  [monoidal : MonoidalCategory (Closed G)]
  [braided : BraidedCategory (Closed G)]
  [symmetric : SymmetricCategory (Closed G)]
  unit_eq : (𝟙_ (Closed G)) = ForgetEnrichment.of _ G.unit
  tensor_obj : ∀ E K : G.category,
    (ForgetEnrichment.of _ E : Closed G) ⊗ (ForgetEnrichment.of _ K) =
      ForgetEnrichment.of _ (tensor.obj (E, K))
  tensor_hom : ∀ (E E' K K' : Closed G) (f : E ⟶ E') (g : K ⟶ K'),
    HEq (dgClosedHom (LargeScalar k) (f ⊗ₘ g))
      (tensor.dgMap 0 (dgTensorHom (LargeScalar k)
        (X := (ForgetEnrichment.to _ E, ForgetEnrichment.to _ K))
        (Y := (ForgetEnrichment.to _ E', ForgetEnrichment.to _ K'))
        (p := 0) (q := 0) (n := 0)
        (dgClosedHom (LargeScalar k) f) (dgClosedHom (LargeScalar k) g) (by omega)))

variable {U : RegularUnitSystem M} {X : Prestack k} {G : QCohEnhancement M U X}
    {T : TensorFibrationModel M} {F : TensorSectionModel M T X}

/-- The actual left unitor, transported through the normalized tensor and unit objects. -/
def leftUnitor (H : MonoidalEnhancement G F) (E : G.category) :
    (ForgetEnrichment.of _ (H.tensor.obj (G.unit, E)) : Closed G) ⟶ ForgetEnrichment.of _ E := by
  letI := H.monoidal
  exact eqToHom (H.tensor_obj G.unit E).symm ≫
    (eqToHom H.unit_eq.symm ⊗ₘ 𝟙 _) ≫ (λ_ (ForgetEnrichment.of _ E : Closed G)).hom

/-- The actual right unitor is fixed by the same structure unit and tensor. -/
def rightUnitor (H : MonoidalEnhancement G F) (E : G.category) :
    (ForgetEnrichment.of _ (H.tensor.obj (E, G.unit)) : Closed G) ⟶ ForgetEnrichment.of _ E := by
  letI := H.monoidal
  exact eqToHom (H.tensor_obj E G.unit).symm ≫
    (𝟙 _ ⊗ₘ eqToHom H.unit_eq.symm) ≫ (ρ_ (ForgetEnrichment.of _ E : Closed G)).hom

/-- The actual symmetry morphism of the normalized global tensor. -/
def symmetry (H : MonoidalEnhancement G F) (E K : G.category) :
    (ForgetEnrichment.of _ (H.tensor.obj (E, K)) : Closed G) ⟶
      ForgetEnrichment.of _ (H.tensor.obj (K, E)) := by
  letI := H.monoidal
  letI := H.braided
  exact eqToHom (H.tensor_obj E K).symm ≫
    (β_ (ForgetEnrichment.of _ E : Closed G) (ForgetEnrichment.of _ K)).hom ≫
      eqToHom (H.tensor_obj K E)

/-- The actual global associator retains all three source tensor objects. -/
def associator (H : MonoidalEnhancement G F) (A E K : G.category) :
    (ForgetEnrichment.of _ (H.tensor.obj (H.tensor.obj (A, E), K)) : Closed G) ⟶
      ForgetEnrichment.of _ (H.tensor.obj (A, H.tensor.obj (E, K))) := by
  letI := H.monoidal
  exact eqToHom (H.tensor_obj (H.tensor.obj (A, E)) K).symm ≫
    (eqToHom (H.tensor_obj A E).symm ⊗ₘ 𝟙 _) ≫
      (α_ (ForgetEnrichment.of _ A : Closed G) (ForgetEnrichment.of _ E)
        (ForgetEnrichment.of _ K)).hom ≫
      (𝟙 _ ⊗ₘ eqToHom (H.tensor_obj E K)) ≫
        eqToHom (H.tensor_obj A (H.tensor.obj (E, K)))

/-- The unit diagonal is the actual unitor inverse in the normalized tensor. -/
def unitDiagonal (H : MonoidalEnhancement G F) :
    (ForgetEnrichment.of _ G.unit : Closed G) ⟶
      ForgetEnrichment.of _ (H.tensor.obj (G.unit, G.unit)) := by
  letI := H.monoidal
  exact (λ_ (ForgetEnrichment.of _ G.unit : Closed G)).inv ≫
    (eqToHom H.unit_eq ⊗ₘ 𝟙 _) ≫ eqToHom (H.tensor_obj G.unit G.unit)

/-- RΓ(E)⊗RΓ(K)→RΓ(E⊗K) uses the actual enriched tensor and native unit diagonal. -/
def cup (H : MonoidalEnhancement G F) (E K : G.category) :
    globalHom G E ⊗ globalHom G K ⟶ globalHom G (H.tensor.obj (E, K)) :=
  H.tensor.map (G.unit, G.unit) (E, K) ≫
    eHomWhiskerRight (Cochains (LargeScalar k)) (unitDiagonal H)
      (ForgetEnrichment.of _ (H.tensor.obj (E, K)) : Closed G)

/-- The dual triangle is computed using the actual unitors, associator and
closed evaluation/coevaluation representatives. -/
def dualTriangle (H : MonoidalEnhancement G F) (D E : G.category)
    (c : (ForgetEnrichment.of _ G.unit : Closed G) ⟶
      ForgetEnrichment.of _ (H.tensor.obj (D, E)))
    (e : (ForgetEnrichment.of _ (H.tensor.obj (E, D)) : Closed G) ⟶
      ForgetEnrichment.of _ G.unit) :
    (ForgetEnrichment.of _ D : Closed G) ⟶ ForgetEnrichment.of _ D := by
  letI := H.monoidal
  let X := (ForgetEnrichment.of _ D : Closed G)
  let Y := (ForgetEnrichment.of _ E : Closed G)
  let c' : (𝟙_ (Closed G)) ⟶ X ⊗ Y :=
    eqToHom H.unit_eq ≫ c ≫ eqToHom (H.tensor_obj D E).symm
  let e' : Y ⊗ X ⟶ (𝟙_ (Closed G)) :=
    eqToHom (H.tensor_obj E D) ≫ e ≫ eqToHom H.unit_eq.symm
  exact (λ_ X).inv ≫ c' ▷ X ≫ (α_ X Y X).hom ≫ X ◁ e' ≫ (ρ_ X).hom

/-- The object triangle uses those same representatives and native associator. -/
def objectTriangle (H : MonoidalEnhancement G F) (D E : G.category)
    (c : (ForgetEnrichment.of _ G.unit : Closed G) ⟶
      ForgetEnrichment.of _ (H.tensor.obj (D, E)))
    (e : (ForgetEnrichment.of _ (H.tensor.obj (E, D)) : Closed G) ⟶
      ForgetEnrichment.of _ G.unit) :
    (ForgetEnrichment.of _ E : Closed G) ⟶ ForgetEnrichment.of _ E := by
  letI := H.monoidal
  let X := (ForgetEnrichment.of _ D : Closed G)
  let Y := (ForgetEnrichment.of _ E : Closed G)
  let c' : (𝟙_ (Closed G)) ⟶ X ⊗ Y :=
    eqToHom H.unit_eq ≫ c ≫ eqToHom (H.tensor_obj D E).symm
  let e' : Y ⊗ X ⟶ (𝟙_ (Closed G)) :=
    eqToHom (H.tensor_obj E D) ≫ e ≫ eqToHom H.unit_eq.symm
  exact (ρ_ Y).inv ≫ Y ◁ c' ≫ (α_ Y X Y).inv ≫ e' ▷ Y ≫ (λ_ Y).hom

/-- A closed endomorphism retains its actual degree-zero enriched carrier. -/
def closedEndomorphism (E : G.category)
    (f : (ForgetEnrichment.of (Cochains (LargeScalar k)) E : Closed G) ⟶
      ForgetEnrichment.of (Cochains (LargeScalar k)) E) : DGHom (LargeScalar k) 0 E E :=
  dgClosedHom (LargeScalar k) f

/-- A perfect dual has actual closed evaluation and coevaluation maps.
The two native triangles hold through specified degree-minus-one DG
homotopies; arbitrary cofibrant representatives need not be strictly dualizable. -/
structure PerfectDual (H : MonoidalEnhancement G F) (E : G.category) where
  object : G.category
  coevaluation : (ForgetEnrichment.of _ G.unit : Closed G) ⟶
    ForgetEnrichment.of _ (H.tensor.obj (object, E))
  evaluation : (ForgetEnrichment.of _ (H.tensor.obj (E, object)) : Closed G) ⟶
    ForgetEnrichment.of _ G.unit
  dualHomotopy : DGHom (LargeScalar k) (-1) object object
  dual_triangle : castDeg (LargeScalar k) (by omega : (-1 : ℤ) + 1 = 0)
    (dgDifferential (LargeScalar k) (-1) dualHomotopy) =
      closedEndomorphism object (dualTriangle H object E coevaluation evaluation) -
        dgId (LargeScalar k) object
  objectHomotopy : DGHom (LargeScalar k) (-1) E E
  object_triangle : castDeg (LargeScalar k) (by omega : (-1 : ℤ) + 1 = 0)
    (dgDifferential (LargeScalar k) (-1) objectHomotopy) =
      closedEndomorphism E (objectTriangle H object E coevaluation evaluation) -
        dgId (LargeScalar k) E
  perfect : IsPerfect G object

/-- The source evaluation of E with E∨, with the global tensor and unit fixed. -/
def evaluation (H : MonoidalEnhancement G F) {E : G.category} (D : PerfectDual H E) :
    (ForgetEnrichment.of _ (H.tensor.obj (E, D.object)) : Closed G) ⟶
      ForgetEnrichment.of _ G.unit := D.evaluation

/-- The actual coevaluation representative of the same homotopy dual. -/
def coevaluation (H : MonoidalEnhancement G F) {E : G.category} (D : PerfectDual H E) :
    (ForgetEnrichment.of _ G.unit : Closed G) ⟶
      ForgetEnrichment.of _ (H.tensor.obj (D.object, E)) := D.coevaluation

/-- The actual global dual pairing is cup followed by this same evaluation. -/
def sectionPairing (H : MonoidalEnhancement G F) {E : G.category} (D : PerfectDual H E) :
    globalHom G E ⊗ globalHom G D.object ⟶ globalHom G G.unit :=
  cup H E D.object ≫
    eHomWhiskerLeft (Cochains (LargeScalar k)) (ForgetEnrichment.of _ G.unit : Closed G)
      (evaluation H D)

end MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
