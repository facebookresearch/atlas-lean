/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedSourceRelativeIsotropicMaps
public import MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
public import MathlibExt.AlgebraicGeometry.DerivedSourcedOrientations

/-!
# Native mapping cotangents and evaluation-normalized tangent comparison

The mapping tangent is the dual of its independently represented actual
square-zero cotangent. The partial evaluation differential is normalized
on the full coefficient-test Hom/derivation fibrations, with X held
fixed. X is not required to have a perfect cotangent or to be Artin.

Its dual mate and the full enriched adjunction to actual product
pullback compute T_Map to p_*ev*T_F. The right adjoint is defined on
every QCoh object and every homogeneous Hom, so p_* is actual derived
RΓ in the X direction. The explicit affine coefficient front door is
the same native RΓ_X_A of the literal evaluation pullback.

Source: PTVV arXiv:1111.3209v4, Theorem 2.5 and its proof, pp.33--35;
HAG II arXiv:math/0404373v7, Section 1.4.1. Native notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSourceMappingTangents

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open _root_.CategoryTheory.MonoidalCategory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.PerfectDGModuleModels
open MathlibExt.CategoryTheory.NativeDGNerveModels
open MathlibExt.AlgebraicTopology.SimplicialCovariantModels
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.DerivedPrestackEvaluation
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
open MathlibExt.AlgebraicGeometry.DerivedCoherentCotangentModels
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedCoherentExteriorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedRelativeTangentModels
open MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedCompactOrientations
open MathlibExt.AlgebraicGeometry.DerivedCoefficientTensorModels
open MathlibExt.AlgebraicGeometry.DerivedGammaTensorModels
open MathlibExt.AlgebraicGeometry.DerivedSourcedCechModels
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] [Algebra ℚ k]
    {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {NC : MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams.NegativeCyclicDiagram
      D.functor (2 : ℤ)} {N : ShuffleAlgebraFunctor k} {S : AffineScalarSystem N}
    {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {R : RawModuleRealization M} {L : CochainLiftModel k}

/-- Native postcomposition keeps every source-fixed coherent simplex of the left slice. -/
def mapLeftSlice {A B : SSet.{u + 1}} (f : A ⟶ B) {x : A _⦋0⦌} {y : B _⦋0⦌}
    (h : f.app (op ⦋0⦌) x = y) : leftSlice A x ⟶ leftSlice B y where
  app n := ↾fun a => ⟨f.app _ a.val, by
    have hn := congrArg (fun t => t a.val) (f.naturality (initialVertex n.unop).op)
    change f.app (op ⦋0⦌) (A.map (initialVertex n.unop).op a.val) =
      B.map (initialVertex n.unop).op (f.app _ a.val) at hn
    change B.map (initialVertex n.unop).op (f.app _ a.val) = y
    rw [← hn, a.property, h]⟩
  naturality n m g := by
    ext a
    apply Subtype.ext
    change f.app _ (A.map (prepend.map g.unop).op a.val) =
      B.map (prepend.map g.unop).op (f.app _ a.val)
    exact congrArg (fun t => t a.val) (f.naturality (prepend.map g.unop).op)

/-- Native postcomposition preserves the entire target projection. -/
theorem mapLeftSlice_over {A B : SSet.{u + 1}} (f : A ⟶ B) {x : A _⦋0⦌} {y : B _⦋0⦌}
    (h : f.app (op ⦋0⦌) x = y) :
    mapLeftSlice f h ≫ targetProjection B y = targetProjection A x ≫ f := by
  ext n a
  change B.map (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op (f.app _ a.val) =
    f.app _ (A.map (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op a.val)
  exact (congrArg (fun t => t a.val)
    (f.naturality (SimplexCategory.δ (0 : Fin (n.unop.len + 2))).op)).symm

variable {X F : Prestack k} {RF : FibrantReplacement F}
    (E : EvaluationModel Q X F RF)

/-- Mapping-family product projection retains every coefficient, mapping and gauge simplex. -/
def mappingProjection : mappingPrestackFunctor k Q X F RF ⊗ X ⟶
    mappingPrestackFunctor k Q X F RF := productProjection _ _

/-- A full enriched right adjoint to the actual QCoh pullback is derived pushforward;
its all-degree Hom formulas fix the RΓ operator independently of any tangent endpoint. -/
structure MappingPushforward {A B : Prestack k} {GA : QCohEnhancement M U A}
    {GB : QCohEnhancement M U B} {p : B ⟶ A} (PB : PullbackDGModel p GA GB) where
  functor : EnrichedFunctor (Cochains (LargeScalar k)) GB.category GA.category
  hom : ∀ (V : GA.category) (W : GB.category),
    dgHomComplex (LargeScalar k) (PB.functor.obj V) W ≅
      dgHomComplex (LargeScalar k) V (functor.obj W)
  sourceNatural : ∀ (V V' : GA.category) (W : GB.category) (p q r : ℤ)
    (a : DGHom (LargeScalar k) p V' V) (b : DGHom (LargeScalar k) q (PB.functor.obj V) W)
    (h : p + q = r),
    ((hom V' W).hom.f r).hom (dgComp (LargeScalar k) (PB.functor.dgMap p a) b h) =
      dgComp (LargeScalar k) a (((hom V W).hom.f q).hom b) h
  targetNatural : ∀ (V : GA.category) (W W' : GB.category) (p q r : ℤ)
    (a : DGHom (LargeScalar k) p (PB.functor.obj V) W) (b : DGHom (LargeScalar k) q W W')
    (h : p + q = r),
    ((hom V W').hom.f r).hom (dgComp (LargeScalar k) a b h) =
      dgComp (LargeScalar k) (((hom V W).hom.f p).hom a) (functor.dgMap q b) h

/-- The relative evaluation test Hom keeps the original entire Map coefficient-test base. -/
def mappingTestHom
    (SM : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC)
      (mappingPrestackFunctor k Q X F RF))
    (GP : QCohEnhancement M U (mappingPrestackFunctor k Q X F RF ⊗ X))
    (PB : PullbackDGModel (mappingProjection (Q := Q) (X := X) (F := F) (RF := RF)) SM.global GP)
    (W : GP.category) :=
  pullback (targetProjection (dgNerve (k := LargeScalar k) GP.category) (objectVertex W))
    (SM.context.dgKernels.map ≫ dgNerveMap PB.functor)

/-- Every relative Hom simplex retains its actual Map coefficient test. -/
def mappingTestHomProjection
    (SM : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC)
      (mappingPrestackFunctor k Q X F RF))
    (GP : QCohEnhancement M U (mappingPrestackFunctor k Q X F RF ⊗ X))
    (PB : PullbackDGModel (mappingProjection (Q := Q) (X := X) (F := F) (RF := RF)) SM.global GP)
    (W : GP.category) : mappingTestHom SM GP PB W ⟶
      nerve (CoefficientTest M R SM.context.kernels) := pullback.snd _ _

/-- The relative evaluation cotangent is represented over the SAME actual square-zero Map tests. -/
structure MappingRelativeEvaluation
    (SM : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC)
      (mappingPrestackFunctor k Q X F RF))
    (ST : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) RF.model)
    (GP : QCohEnhancement M U (mappingPrestackFunctor k Q X F RF ⊗ X))
    (PB : PullbackDGModel (mappingProjection (Q := Q) (X := X) (F := F) (RF := RF)) SM.global GP)
    (EV : PullbackDGModel E.map ST.global GP) where
  representation : mappingTestHom SM GP PB (EV.functor.obj ST.context.cotangent.object) ⟶
    SM.context.fibration.total
  over : representation ≫ SM.context.fibration.projection =
    mappingTestHomProjection SM GP PB (EV.functor.obj ST.context.cotangent.object)
  weak : ∀ t : CoefficientTest M R SM.context.kernels,
    MathlibExt.AlgebraicGeometry.SimplicialDerivedModels.WeakEquivalence
      (MathlibExt.AlgebraicTopology.SimplicialCovariantModels.fibreMap
        (mappingTestHomProjection SM GP PB (EV.functor.obj ST.context.cotangent.object))
        SM.context.fibration.projection representation over (ComposableArrows.mk₀ t))

/-- The partial differential is fixed on entire Hom/actual square-zero derivation fibrations. -/
structure MappingPartialDifferential
    (SM : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC)
      (mappingPrestackFunctor k Q X F RF))
    (ST : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) RF.model)
    (GP : QCohEnhancement M U (mappingPrestackFunctor k Q X F RF ⊗ X))
    (PB : PullbackDGModel (mappingProjection (Q := Q) (X := X) (F := F) (RF := RF)) SM.global GP)
    (EV : PullbackDGModel E.map ST.global GP)
    (C : MappingRelativeEvaluation E SM ST GP PB EV) where
  map : DGHom (LargeScalar k) 0 (EV.functor.obj ST.context.cotangent.object)
    (PB.functor.obj SM.context.cotangent.object)
  closed : map ∈ dgCycles (LargeScalar k) _ _
  precomposition : SlicePrecomposition map closed
  source_vertex : (dgNerveMap PB.functor).app (op ⦋0⦌)
    (objectVertex SM.context.cotangent.object) = objectVertex (PB.functor.obj SM.context.cotangent.object)
  source : homFamily SM.context.dgKernels SM.context.cotangent.object ⟶
    mappingTestHom SM GP PB (PB.functor.obj SM.context.cotangent.object)
  source_normalized : source ≫ pullback.fst _ _ =
    pullback.fst _ _ ≫ mapLeftSlice (dgNerveMap PB.functor) source_vertex
  source_over : source ≫ mappingTestHomProjection SM GP PB (PB.functor.obj SM.context.cotangent.object) =
    homFamilyProjection SM.context.dgKernels SM.context.cotangent.object
  transpose : mappingTestHom SM GP PB (PB.functor.obj SM.context.cotangent.object) ⟶
    mappingTestHom SM GP PB (EV.functor.obj ST.context.cotangent.object)
  transpose_normalized : transpose ≫ pullback.fst _ _ = pullback.fst _ _ ≫ precomposition.map
  transpose_over : transpose ≫ mappingTestHomProjection SM GP PB (EV.functor.obj ST.context.cotangent.object) =
    mappingTestHomProjection SM GP PB (PB.functor.obj SM.context.cotangent.object)
  normalized : SSet.Edge (X := mappingOver
      (homFamilyProjection SM.context.dgKernels SM.context.cotangent.object) SM.context.fibration.projection)
    (overMapVertex _ _ (source ≫ transpose ≫ C.representation) (by
      rw [Category.assoc, Category.assoc, C.over, transpose_over, source_over]))
    (overMapVertex _ _ SM.context.cotangent.map SM.context.cotangent.over)

/-- A pulled perfect pair has its original evaluation and coevaluation, with the full native tensor source. -/
structure MappingPulledPair {A B : Prestack k}
    (SA : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) A)
    (GB : QCohEnhancement M U B) (HB : CoherentMonoidalEnhancement GB)
    {f : B ⟶ A} (PB : PullbackDGModel f SA.global GB) where
  unit : PB.functor.obj SA.global.unit = GB.unit
  tensor : TensorPullbackSource SA.monoidal HB PB
  inverse : ∀ V W : SA.global.category,
    DGHom (LargeScalar k) 0 (HB.monoidal.tensor.obj (PB.functor.obj V, PB.functor.obj W))
      (PB.functor.obj (SA.monoidal.monoidal.tensor.obj (V,W)))
  inverse_closed : ∀ V W, inverse V W ∈ dgCycles (LargeScalar k) _ _
  inverseHomotopy : ∀ V W : SA.global.category,
    DGHom (LargeScalar k) (-1) (HB.monoidal.tensor.obj (PB.functor.obj V, PB.functor.obj W))
      (HB.monoidal.tensor.obj (PB.functor.obj V, PB.functor.obj W))
  inverseIdentity : ∀ V W,
    dgDifferential (LargeScalar k) (-1) (inverseHomotopy V W) =
      dgComp (LargeScalar k) (inverse V W) (tensor.map V W) (by omega) -
        dgId (LargeScalar k) (HB.monoidal.tensor.obj (PB.functor.obj V, PB.functor.obj W))
  forwardHomotopy : ∀ V W : SA.global.category,
    DGHom (LargeScalar k) (-1) (PB.functor.obj (SA.monoidal.monoidal.tensor.obj (V,W)))
      (PB.functor.obj (SA.monoidal.monoidal.tensor.obj (V,W)))
  forwardIdentity : ∀ V W,
    dgDifferential (LargeScalar k) (-1) (forwardHomotopy V W) =
      dgComp (LargeScalar k) (tensor.map V W) (inverse V W) (by omega) -
        dgId (LargeScalar k) (PB.functor.obj (SA.monoidal.monoidal.tensor.obj (V,W)))
  pair : PerfectDual HB.monoidal (PB.functor.obj SA.context.cotangent.object)
  tangent : pair.object = PB.functor.obj SA.tangent.object
  evaluation : HEq (dgClosedHom (LargeScalar k) pair.evaluation)
    (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
      (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0) (inverse SA.context.cotangent.object SA.tangent.object)
        (PB.functor.dgMap 0 (dgClosedHom (LargeScalar k) SA.tangent.evaluation)) (by omega))
      (dgClosedHom (LargeScalar k) (eqToHom
        (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k))) unit))) (by omega))
  coevaluation : HEq (dgClosedHom (LargeScalar k) pair.coevaluation)
    (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
      (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0) (dgClosedHom (LargeScalar k) (eqToHom
        (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k))) unit.symm)))
        (PB.functor.dgMap 0 (dgClosedHom (LargeScalar k) SA.tangent.coevaluation)) (by omega))
      (tensor.map SA.tangent.object SA.context.cotangent.object) (by omega))

/-- Mapping source choices retain the independent Map cotangent and literal full evaluation.
No perfect cotangent on X and no target tangent-comparison equivalence is required. -/
structure MappingTangentSources (E : EvaluationModel Q X F RF) where
  mapping : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC)
    (mappingPrestackFunctor k Q X F RF)
  target : CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) RF.model
  product : QCohEnhancement M U (mappingPrestackFunctor k Q X F RF ⊗ X)
  productCech : GammaCechData L product
  productSource : SourceEnrichedQCohModel productCech.category product R productCech.source productCech.unit
  monoidal : CoherentMonoidalEnhancement product
  projection : PullbackDGModel (mappingProjection (Q := Q) (X := X) (F := F) (RF := RF)) mapping.global product
  evaluation : PullbackDGModel E.map target.global product
  relative : MappingRelativeEvaluation E mapping target product projection evaluation
  differential : MappingPartialDifferential E mapping target product projection evaluation relative
  mappingPair : MappingPulledPair mapping product monoidal projection
  targetPair : MappingPulledPair target product monoidal evaluation
  pushforward : MappingPushforward projection

/-- The actual p_*ev*T_F, i.e. native RΓ in the X direction, uses the full enriched right adjoint. -/
def evaluationGamma (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E) :=
  B.pushforward.functor.obj (B.evaluation.functor.obj B.target.tangent.object)

/-- The coefficient map is the actual native dual mate of relative evaluation, with both source pairings. -/
def partialEvaluationTangent (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E) :
    DGHom (LargeScalar k) 0 (B.projection.functor.obj B.mapping.tangent.object)
      (B.evaluation.functor.obj B.target.tangent.object) :=
  dgClosedHom (LargeScalar k)
    (eqToHom (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k))) B.mappingPair.tangent.symm) ≫
      dualDifferential B.monoidal B.differential.map B.differential.closed
        B.mappingPair.pair B.targetPair.pair ≫
      eqToHom (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k))) B.targetPair.tangent))

/-- The mapping tangent comparison is the full enriched adjoint transpose of that computed evaluation map. -/
def mappingTangentComparison (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E) :
    DGHom (LargeScalar k) 0 B.mapping.tangent.object (evaluationGamma E B) :=
  (((B.pushforward.hom B.mapping.tangent.object
    (B.evaluation.functor.obj B.target.tangent.object)).hom.f 0).hom (partialEvaluationTangent E B))

/-- The full enriched adjunction is a cochain isomorphism, so the computed transpose is closed. -/
theorem mappingTangentComparison_closed
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E) :
    dgDifferential (LargeScalar k) 0 (mappingTangentComparison E B) = 0 := by
  let I := B.pushforward.hom B.mapping.tangent.object
    (B.evaluation.functor.obj B.target.tangent.object)
  have hp : dgDifferential (LargeScalar k) 0 (partialEvaluationTangent E B) = 0 :=
    (mem_dgCycles (LargeScalar k)).mp (dgClosedHom_mem_dgCycles (LargeScalar k) _)
  have h := congrArg (fun f => f.hom (partialEvaluationTangent E B)) (I.hom.comm 0 1)
  change dgDifferential (LargeScalar k) 0 (mappingTangentComparison E B) =
    (I.hom.f 1).hom (dgDifferential (LargeScalar k) 0 (partialEvaluationTangent E B)) at h
  rw [hp, map_zero] at h
  exact h

/-- The actual affine evaluation is the literal f times identity of X followed by the original evaluation. -/
def affineMappingEvaluation (A : SAlg k)
    (f : affineMapping k Q A ⟶ mappingPrestackFunctor k Q X F RF) : baseChanged Q X A ⟶ RF.model :=
  (f ⊗ₘ 𝟙 X) ≫ E.map

/-- Explicit coefficient RΓ_X_A(f*T_F), with actual full A-module action and native evaluation pullback. -/
def affineEvaluationGamma {V : NerveLiftModel L} (BX : FamilyModel M U Q L V X)
    (B : MappingTangentSources (U := U) (R := R) (L := L) (D := D) (NC := NC) E)
    (A : SAlg k) (f : affineMapping k Q A ⟶ mappingPrestackFunctor k Q X F RF)
    (P : PullbackDGModel (affineMappingEvaluation E A f) B.target.global (BX.model A)) :=
  gamma BX A (P.functor.obj B.target.tangent.object)

end MathlibExt.AlgebraicGeometry.DerivedSourceMappingTangents
