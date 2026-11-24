/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
public import MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence
public import MathlibExt.AlgebraicGeometry.CoherentNerveTransformations

/-!
# Source-normalized monoidal coherence for actual QCoh tensors

Affine unitors, symmetry and associators use the actual module actions,
Koszul quotient map and nested quotient generators. Their nerve paths
are realized from closed DG natural families with all homogeneous
naturality and every joint coherent-frame coefficient fixed.

The fibration and global section comparisons retain these entire
parameterized maps. No independent affine coherence isomorphisms or
global unit/symmetry/associator paths are accepted as source evidence.
Generic coherent assembly remains explicit construction work.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorCoherence
open MathlibExt.AlgebraicGeometry.DerivedCoefficientDualModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.CoherentNerveTransformations
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedAffineFamilies
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u
variable {R : Type u} [CommRing R] (C : DGCat R) (o : C)

/-- An actual module morphism is its native closed homogeneous DG component. -/
def moduleCycle {M N : RightModule R C} (f : M ⟶ N) : DGHom R 0 M N :=
  ((DGFunctor.homEquivDGCycles R M N) f).val

variable (T : DerivedTensorModel C o) (P : NerveTensorModel T.functor)
    (unit : DGDerivedModules R C) (unit_eq : unit.obj = regularModule C o)
    (K : CoherenceModel C o T unit unit_eq)

/-- Every affine coherence path realizes the actual quotient-map DG transformation. -/
structure AffineCoherenceNerves where
  left : ∀ M : DGDerivedModules R C,
    DGHom R 0 ((P.fixedLeft unit).functor.obj M) M
  left_component : ∀ M : DGDerivedModules R C,
    HEq (left M) (moduleCycle C (K.leftUnit M).hom)
  leftNerve : NerveTransformationModel (P.fixedLeft unit).functor
    (EnrichedFunctor.id (Cochains R) (DGDerivedModules R C)) left
  right : ∀ M : DGDerivedModules R C,
    DGHom R 0 ((P.fixedRight unit).functor.obj M) M
  right_component : ∀ M : DGDerivedModules R C,
    HEq (right M) (moduleCycle C (K.rightUnit M).hom)
  rightNerve : NerveTransformationModel (P.fixedRight unit).functor
    (EnrichedFunctor.id (Cochains R) (DGDerivedModules R C)) right
  swap : SwapDGFunctorModel (R := R) (DGDerivedModules R C)
  symmetry : ∀ x : (DGDerivedModules R C) × (DGDerivedModules R C),
    DGHom R 0 (T.functor.obj x) ((swap.functor.comp (Cochains R) T.functor).obj x)
  symmetry_component : ∀ M N : DGDerivedModules R C,
    HEq (symmetry (M, N)) (moduleCycle C (K.symmetry M N).hom)
  symmetryNerve : NerveTransformationModel T.functor
    (swap.functor.comp (Cochains R) T.functor) symmetry
  leftProduct : ProductDGFunctorModel T.functor
    (EnrichedFunctor.id (Cochains R) (DGDerivedModules R C))
  rightProduct : ProductDGFunctorModel
    (EnrichedFunctor.id (Cochains R) (DGDerivedModules R C)) T.functor
  rebracket : AssociatorDGFunctorModel (R := R) (DGDerivedModules R C)
  associator : ∀ x : ((DGDerivedModules R C) × (DGDerivedModules R C)) × (DGDerivedModules R C),
    DGHom R 0 ((leftProduct.functor.comp (Cochains R) T.functor).obj x)
      (((rebracket.functor.comp (Cochains R) rightProduct.functor).comp
        (Cochains R) T.functor).obj x)
  associator_component : ∀ A M N : DGDerivedModules R C,
    HEq (associator ((A, M), N)) (moduleCycle C (K.associator A M N).hom)
  associatorNerve : NerveTransformationModel (leftProduct.functor.comp (Cochains R) T.functor)
    ((rebracket.functor.comp (Cochains R) rightProduct.functor).comp (Cochains R) T.functor)
    associator
  pair : PairNerveModel (R := R) (C := DGDerivedModules R C) (D := DGDerivedModules R C)
  triplePair : PairNerveModel (R := R)
    (C := (DGDerivedModules R C) × (DGDerivedModules R C)) (D := DGDerivedModules R C)

/-- The full affine symmetry path uses the joint product frame followed by the actual DG swap. -/
def symmetryReference (B : AffineCoherenceNerves C o T P unit unit_eq K) :
    (dgNerve (k := R) (DGDerivedModules R C) ⊗ dgNerve (k := R) (DGDerivedModules R C)) ⊗
        Δ[1] ⟶ dgNerve (k := R) (DGDerivedModules R C) :=
  (B.pair.map ⊗ₘ 𝟙 _) ≫ B.symmetryNerve.map

/-- The full affine associator path retains all three tensor inputs and the interval. -/
def associatorReference (B : AffineCoherenceNerves C o T P unit unit_eq K) :
    ((dgNerve (k := R) (DGDerivedModules R C) ⊗ dgNerve (k := R) (DGDerivedModules R C)) ⊗
        dgNerve (k := R) (DGDerivedModules R C)) ⊗ Δ[1] ⟶
      dgNerve (k := R) (DGDerivedModules R C) :=
  (((B.pair.map ⊗ₘ 𝟙 _) ≫ B.triplePair.map) ⊗ₘ 𝟙 _) ≫ B.associatorNerve.map

section Fibration

variable {k : Type u} [CommRing k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} (M : AffineModuleFibration N S)
    (U : RegularUnitSystem M) (F : TensorFibrationModel M)

/-- The actual coefficient unit in the source affine module category. -/
def affineUnit (A : SAlg k) : DGDerivedModules k (coefficientCategory N A) :=
  ⟨regularModule (coefficientCategory N A) PUnit.unit, U.cofibrant A⟩

/-- Insert the same regular unit system in the first tensor factor. -/
def leftUnitPair : M.total ⟶ pullback M.projection M.projection :=
  pullback.lift (M.projection ≫ U.map) (𝟙 M.total) (by
    rw [Category.assoc, U.projection, Category.comp_id, Category.id_comp])

/-- Insert that regular unit system in the second tensor factor. -/
def rightUnitPair : M.total ⟶ pullback M.projection M.projection :=
  pullback.lift (𝟙 M.total) (M.projection ≫ U.map) (by
    rw [Category.assoc, U.projection, Category.comp_id, Category.id_comp])

/-- The native factor-swap map of the actual fibre product. -/
def swapPair : pullback M.projection M.projection ⟶ pullback M.projection M.projection :=
  pullback.lift (pullback.snd M.projection M.projection)
    (pullback.fst M.projection M.projection) (pullback.condition.symm)

/-- The actual scalar projection of a compatible module pair. -/
def pairProjection : pullback M.projection M.projection ⟶ nerve (SAlg k) :=
  pullback.fst M.projection M.projection ≫ M.projection

/-- The actual compatible triple of modules over one scalar algebra. -/
def tripleObject := pullback (pairProjection M) M.projection

/-- Left and right parenthesized pair maps are fixed by all three native projections. -/
structure TripleTensorModel where
  lastPair : tripleObject M ⟶ pullback M.projection M.projection
  lastPair_fst : lastPair ≫ pullback.fst M.projection M.projection =
    pullback.fst (pairProjection M) M.projection ≫ pullback.snd M.projection M.projection
  lastPair_snd : lastPair ≫ pullback.snd M.projection M.projection =
    pullback.snd (pairProjection M) M.projection
  left : tripleObject M ⟶ pullback M.projection M.projection
  left_fst : left ≫ pullback.fst M.projection M.projection =
    pullback.fst (pairProjection M) M.projection ≫ F.map
  left_snd : left ≫ pullback.snd M.projection M.projection =
    pullback.snd (pairProjection M) M.projection
  right : tripleObject M ⟶ pullback M.projection M.projection
  right_fst : right ≫ pullback.fst M.projection M.projection =
    pullback.fst (pairProjection M) M.projection ≫ pullback.fst M.projection M.projection
  right_snd : right ≫ pullback.snd M.projection M.projection = lastPair ≫ F.map

/-- The whole module-fibration coherence is fixed by the actual affine cochain maps. -/
structure FibrationCoherenceModel where
  affine : ∀ A : SAlg k,
    CoherenceModel (coefficientCategory N A) PUnit.unit (F.affine A) (affineUnit M U A) rfl
  nerves : ∀ A : SAlg k,
    AffineCoherenceNerves (coefficientCategory N A) PUnit.unit (F.affine A) (F.nerve A)
      (affineUnit M U A) rfl (affine A)
  triple : TripleTensorModel M F
  leftUnit : M.total ⊗ Δ[1] ⟶ M.total
  leftUnit_zero : parameterAt M.total 0 ≫ leftUnit = leftUnitPair M U ≫ F.map
  leftUnit_one : parameterAt M.total 1 ≫ leftUnit = 𝟙 M.total
  leftUnit_affine : ∀ A : SAlg k,
    ((M.realization A ≫ pullback.fst M.projection (algebraPoint A)) ⊗ₘ 𝟙 _) ≫ leftUnit =
      (nerves A).leftNerve.map ≫ M.realization A ≫ pullback.fst M.projection (algebraPoint A)
  rightUnit : M.total ⊗ Δ[1] ⟶ M.total
  rightUnit_zero : parameterAt M.total 0 ≫ rightUnit = rightUnitPair M U ≫ F.map
  rightUnit_one : parameterAt M.total 1 ≫ rightUnit = 𝟙 M.total
  rightUnit_affine : ∀ A : SAlg k,
    ((M.realization A ≫ pullback.fst M.projection (algebraPoint A)) ⊗ₘ 𝟙 _) ≫ rightUnit =
      (nerves A).rightNerve.map ≫ M.realization A ≫ pullback.fst M.projection (algebraPoint A)
  symmetry : pullback M.projection M.projection ⊗ Δ[1] ⟶ M.total
  symmetry_zero : parameterAt _ 0 ≫ symmetry = F.map
  symmetry_one : parameterAt _ 1 ≫ symmetry = swapPair M ≫ F.map
  symmetry_affine : ∀ A : SAlg k,
    (F.pair A ⊗ₘ 𝟙 _) ≫ symmetry =
      symmetryReference _ _ _ _ _ _ _ (nerves A) ≫ M.realization A ≫
        pullback.fst M.projection (algebraPoint A)
  associator : tripleObject M ⊗ Δ[1] ⟶ M.total
  associator_zero : parameterAt _ 0 ≫ associator = triple.left ≫ F.map
  associator_one : parameterAt _ 1 ≫ associator = triple.right ≫ F.map
  triplePair : ∀ A : SAlg k,
    ((dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A)) ⊗
      dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A))) ⊗
        dgNerve (k := k) (DGDerivedModules k (coefficientCategory N A))) ⟶ tripleObject M
  triplePair_fst : ∀ A : SAlg k,
    triplePair A ≫ pullback.fst (pairProjection M) M.projection =
      tensorLeftProjection _ _ ≫ F.pair A
  triplePair_snd : ∀ A : SAlg k,
    triplePair A ≫ pullback.snd (pairProjection M) M.projection =
      tensorRightProjection _ _ ≫ M.realization A ≫ pullback.fst M.projection (algebraPoint A)
  associator_affine : ∀ A : SAlg k,
    (triplePair A ⊗ₘ 𝟙 _) ≫ associator =
      associatorReference _ _ _ _ _ _ _ (nerves A) ≫ M.realization A ≫
        pullback.fst M.projection (algebraPoint A)

/-- Pair actual simplicial maps on every simplex, without selecting a second product model. -/
def pairMaps {A B Z : SSet.{u + 1}} (f : Z ⟶ A) (g : Z ⟶ B) : Z ⟶ A ⊗ B where
  app n := ↾fun z => (f.app n z, g.app n z)
  naturality _ _ h := by
    ext z
    apply Prod.ext
    · exact congrArg (fun t => t z) (f.naturality h)
    · exact congrArg (fun t => t z) (g.naturality h)

/-- The actual interval parameter at an entire source-family simplex. -/
def intervalAt (X : Prestack k) (n : SimplexCategoryᵒᵖ) (t : (Δ[1] : SSet.{u + 1}).obj n) :
    nerve (Families X) ⊗ SSet.stdSimplex.obj n.unop ⟶ Δ[1] :=
  tensorRightProjection _ _ ≫ SSet.yonedaEquiv.symm t

/-- Global coherence maps are fixed on the whole affine-family and interval parameter. -/
structure CoherenceSectionModel (B : FibrationCoherenceModel M U F) (X : Prestack k)
    (S : TensorSectionModel M F X) where
  leftUnit : qcoh M X ⊗ Δ[1] ⟶ qcoh M X
  leftUnit_normalized : ∀ (n : SimplexCategoryᵒᵖ) (a : (qcoh M X).obj n) (t : (Δ[1]).obj n),
    parameterEvaluation ((leftUnit.app n (a, t)).val) =
      pairMaps (parameterEvaluation a.val) (intervalAt X n t) ≫ B.leftUnit
  rightUnit : qcoh M X ⊗ Δ[1] ⟶ qcoh M X
  rightUnit_normalized : ∀ (n : SimplexCategoryᵒᵖ) (a : (qcoh M X).obj n) (t : (Δ[1]).obj n),
    parameterEvaluation ((rightUnit.app n (a, t)).val) =
      pairMaps (parameterEvaluation a.val) (intervalAt X n t) ≫ B.rightUnit
  symmetry : (qcoh M X ⊗ qcoh M X) ⊗ Δ[1] ⟶ qcoh M X
  symmetry_normalized : ∀ (n : SimplexCategoryᵒᵖ) (a b : (qcoh M X).obj n) (t : (Δ[1]).obj n),
    parameterEvaluation ((symmetry.app n ((a, b), t)).val) =
      pairMaps (S.pair n a b) (intervalAt X n t) ≫ B.symmetry
  triple : ∀ (n : SimplexCategoryᵒᵖ) (_a _b _c : (qcoh M X).obj n),
    nerve (Families X) ⊗ SSet.stdSimplex.obj n.unop ⟶ tripleObject M
  triple_fst : ∀ (n : SimplexCategoryᵒᵖ) (a b c : (qcoh M X).obj n),
    triple n a b c ≫ pullback.fst (pairProjection M) M.projection = S.pair n a b
  triple_snd : ∀ (n : SimplexCategoryᵒᵖ) (a b c : (qcoh M X).obj n),
    triple n a b c ≫ pullback.snd (pairProjection M) M.projection = parameterEvaluation c.val
  associator : ((qcoh M X ⊗ qcoh M X) ⊗ qcoh M X) ⊗ Δ[1] ⟶ qcoh M X
  associator_normalized : ∀ (n : SimplexCategoryᵒᵖ) (a b c : (qcoh M X).obj n) (t : (Δ[1]).obj n),
    parameterEvaluation ((associator.app n (((a, b), c), t)).val) =
      pairMaps (triple n a b c) (intervalAt X n t) ≫ B.associator

end Fibration

section Global

variable {k : Type u} [CommRing k]
    {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N} {M : AffineModuleFibration N S}
    {U : RegularUnitSystem M} {X : Prestack k} {G : QCohEnhancement M U X}
    {F : TensorFibrationModel M} {Fsec : TensorSectionModel M F X}
    {B : FibrationCoherenceModel M U F}

/-- Actual global unit/symmetry/associator maps realize the same full source coherence sections. -/
structure GlobalCoherenceRealization (H : MonoidalEnhancement G Fsec)
    (Z : CoherenceSectionModel M U F B X Fsec) where
  left : ∀ E : G.category, DGHom (LargeScalar k) 0 ((H.nerve.fixedLeft G.unit).functor.obj E) E
  left_component : ∀ E : G.category,
    HEq (left E) (dgClosedHom (LargeScalar k) (DerivedGlobalTensorModels.leftUnitor H E))
  leftNerve : NerveTransformationModel (H.nerve.fixedLeft G.unit).functor
    (EnrichedFunctor.id (Cochains (LargeScalar k)) G.category) left
  left_realization : leftNerve.map ≫ G.realization = (G.realization ⊗ₘ 𝟙 _) ≫ Z.leftUnit
  right : ∀ E : G.category, DGHom (LargeScalar k) 0 ((H.nerve.fixedRight G.unit).functor.obj E) E
  right_component : ∀ E : G.category,
    HEq (right E) (dgClosedHom (LargeScalar k) (DerivedGlobalTensorModels.rightUnitor H E))
  rightNerve : NerveTransformationModel (H.nerve.fixedRight G.unit).functor
    (EnrichedFunctor.id (Cochains (LargeScalar k)) G.category) right
  right_realization : rightNerve.map ≫ G.realization = (G.realization ⊗ₘ 𝟙 _) ≫ Z.rightUnit
  swap : SwapDGFunctorModel (R := LargeScalar k) G.category
  symmetry : ∀ E : G.category × G.category,
    DGHom (LargeScalar k) 0 (H.tensor.obj E) ((swap.functor.comp (Cochains (LargeScalar k)) H.tensor).obj E)
  symmetry_component : ∀ E K : G.category,
    HEq (symmetry (E, K)) (dgClosedHom (LargeScalar k) (DerivedGlobalTensorModels.symmetry H E K))
  symmetryNerve : NerveTransformationModel H.tensor
    (swap.functor.comp (Cochains (LargeScalar k)) H.tensor) symmetry
  pair : PairNerveModel (R := LargeScalar k) (C := G.category) (D := G.category)
  symmetry_realization : (pair.map ⊗ₘ 𝟙 _) ≫ symmetryNerve.map ≫ G.realization =
    ((G.realization ⊗ₘ G.realization) ⊗ₘ 𝟙 _) ≫ Z.symmetry
  leftProduct : ProductDGFunctorModel H.tensor
    (EnrichedFunctor.id (Cochains (LargeScalar k)) G.category)
  rightProduct : ProductDGFunctorModel
    (EnrichedFunctor.id (Cochains (LargeScalar k)) G.category) H.tensor
  rebracket : AssociatorDGFunctorModel (R := LargeScalar k) G.category
  associator : ∀ E : (G.category × G.category) × G.category,
    DGHom (LargeScalar k) 0 ((leftProduct.functor.comp (Cochains (LargeScalar k)) H.tensor).obj E)
      (((rebracket.functor.comp (Cochains (LargeScalar k)) rightProduct.functor).comp
        (Cochains (LargeScalar k)) H.tensor).obj E)
  associator_component : ∀ A E K : G.category,
    HEq (associator ((A, E), K))
      (dgClosedHom (LargeScalar k) (DerivedGlobalTensorModels.associator H A E K))
  associatorNerve : NerveTransformationModel (leftProduct.functor.comp (Cochains (LargeScalar k)) H.tensor)
    ((rebracket.functor.comp (Cochains (LargeScalar k)) rightProduct.functor).comp
      (Cochains (LargeScalar k)) H.tensor) associator
  triplePair : PairNerveModel (R := LargeScalar k)
    (C := G.category × G.category) (D := G.category)
  associator_realization :
    (((pair.map ⊗ₘ 𝟙 _) ≫ triplePair.map) ⊗ₘ 𝟙 _) ≫ associatorNerve.map ≫ G.realization =
      (((G.realization ⊗ₘ G.realization) ⊗ₘ G.realization) ⊗ₘ 𝟙 _) ≫ Z.associator

/-- A global symmetric monoidal enhancement includes the full source coherence realization. -/
structure CoherentMonoidalEnhancement (G : QCohEnhancement M U X) where
  tensorFibration : TensorFibrationModel M
  tensorSections : TensorSectionModel M tensorFibration X
  monoidal : MonoidalEnhancement G tensorSections
  coherence : FibrationCoherenceModel M U tensorFibration
  coherenceSections : CoherenceSectionModel M U tensorFibration coherence X tensorSections
  realization : GlobalCoherenceRealization monoidal coherenceSections

end Global

end MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
