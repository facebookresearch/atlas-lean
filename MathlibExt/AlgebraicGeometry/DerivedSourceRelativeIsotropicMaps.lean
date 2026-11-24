/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources
public import MathlibExt.AlgebraicGeometry.DerivedRelativeTangentModels

/-!
# Source isotropic paths and the actual relative tangent arrow

The cotangent differential is the full source transpose, and its dual
mate is the tangent differential. Pulling the original perfect dual
retains the actual native tensor, unit, evaluation and coevaluation.
The coefficient b is the pulled source Theta followed by df.

The isotropic h is the signed native NC/DK path coefficient corrected
by the same cochain pullback comparison. The comparison is between the
two displayed, computed cochain maps. Its native degree-minus-one
cochain is not an independently selected isotropic endpoint.

The relative tangent is the actual Yoneda cone[-1]. Theta_h is the
literal i*h-c*b arrow of degree n-1. Boundary proofs and compatible
source choices are separate direct Wanted hooks; nondegeneracy is a
property of this fixed arrow.

Source: PTVV arXiv:1111.3209v4, Definitions 2.7--2.8 and Theorem 2.9;
HAG II arXiv:math/0404373v7, Section 1.4.1. Native source notices remain.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.DerivedSourceRelativeIsotropicMaps

open _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.Opposite
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.AlgebraicGeometry.DerivedPrestackMapping
open MathlibExt.AlgebraicGeometry.SimplicialAlgebraGeometry
open MathlibExt.AlgebraicGeometry.DerivedQCohModuleFamilies
open MathlibExt.AlgebraicGeometry.DerivedQCohEnhancementModels
open MathlibExt.AlgebraicGeometry.DerivedSquareZeroFamilies
open MathlibExt.AlgebraicGeometry.DerivedCotangentDifferentials
open MathlibExt.AlgebraicGeometry.DerivedGlobalTensorModels
open MathlibExt.AlgebraicGeometry.DerivedMonoidalCoherenceModels
open MathlibExt.AlgebraicGeometry.DerivedSymplecticContractions
open MathlibExt.AlgebraicGeometry.DerivedGlobalClosedForms
open MathlibExt.AlgebraicGeometry.DerivedClosedFormComplexes
open MathlibExt.AlgebraicGeometry.DerivedGlobalMixedModels
open MathlibExt.AlgebraicGeometry.DerivedCoherentExteriorDiagrams
open MathlibExt.AlgebraicGeometry.DerivedCotangentFormSources
open MathlibExt.AlgebraicGeometry.DerivedNativeContractionSpaces
open MathlibExt.AlgebraicGeometry.DerivedRelativeTangentModels
open MathlibExt.AlgebraicGeometry.DerivedIsotropicResidues
open MathlibExt.AlgebraicTopology.SimplicialAlgebraShuffle
open MathlibExt.Algebra.Homology.WeightedNegativeCyclicDiagrams
open CochainComplex.HomComplex
open scoped Simplicial

universe u
variable {k : Type u} [CommRing k] [Algebra ℚ k]
    {Q : AlgebraReplacementFunctor k} {D : AffineDRSystem Q}
    {NC : NegativeCyclicDiagram D.functor (2 : ℤ)} {N : ShuffleAlgebraFunctor k}
    {S : AffineScalarSystem N} {M : AffineModuleFibration N S} {U : RegularUnitSystem M}
    {R : RawModuleRealization M} {L : CochainLiftModel k} {X Y : Prestack k}

abbrev FormSources (X : Prestack k) :=
  CotangentFormSources (U := U) (R := R) (L := L) (D := D) (NC := NC) X

variable (SX : FormSources (R := R) (L := L) (D := D) (NC := NC) (U := U) X)
    (SY : FormSources (R := R) (L := L) (D := D) (NC := NC) (U := U) Y)

/-- Coupled native source geometry retains the full differential and actual pulled dual pair. -/
structure RelativeGeometry (f : X ⟶ Y) where
  pullback : PullbackDGModel f SY.global SX.global
  unit : pullback.functor.obj SY.global.unit = SX.global.unit
  source : CotangentAlongSource SY.context f pullback
  context_eq : source.context = SX.context
  tensor : TensorPullbackSource SY.monoidal SX.monoidal pullback
  tensorInverse : ∀ E F : SY.global.category,
    DGHom (LargeScalar k) 0 (SX.monoidal.monoidal.tensor.obj
      (pullback.functor.obj E, pullback.functor.obj F))
      (pullback.functor.obj (SY.monoidal.monoidal.tensor.obj (E, F)))
  tensorInverse_closed : ∀ E F : SY.global.category, tensorInverse E F ∈ dgCycles (LargeScalar k) _ _
  inverseHomotopy : ∀ E F : SY.global.category,
    DGHom (LargeScalar k) (-1) (SX.monoidal.monoidal.tensor.obj
      (pullback.functor.obj E, pullback.functor.obj F))
      (SX.monoidal.monoidal.tensor.obj (pullback.functor.obj E, pullback.functor.obj F))
  inverseIdentity : ∀ E F : SY.global.category,
    dgDifferential (LargeScalar k) (-1) (inverseHomotopy E F) =
      dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
        (tensorInverse E F) (tensor.map E F) (by omega) -
        dgId (LargeScalar k) (SX.monoidal.monoidal.tensor.obj
          (pullback.functor.obj E, pullback.functor.obj F))
  forwardHomotopy : ∀ E F : SY.global.category,
    DGHom (LargeScalar k) (-1) (pullback.functor.obj (SY.monoidal.monoidal.tensor.obj (E, F)))
      (pullback.functor.obj (SY.monoidal.monoidal.tensor.obj (E, F)))
  forwardIdentity : ∀ E F : SY.global.category,
    dgDifferential (LargeScalar k) (-1) (forwardHomotopy E F) =
      dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
        (tensor.map E F) (tensorInverse E F) (by omega) -
        dgId (LargeScalar k) (pullback.functor.obj (SY.monoidal.monoidal.tensor.obj (E, F)))
  pulledDual : PerfectDual SX.monoidal.monoidal (pullback.functor.obj SY.context.cotangent.object)
  tangent_eq : pulledDual.object = pullback.functor.obj SY.tangent.object
  evaluation : HEq (dgClosedHom (LargeScalar k) pulledDual.evaluation)
    (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
      (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
        (tensorInverse SY.context.cotangent.object SY.tangent.object)
        (pullback.functor.dgMap 0 (dgClosedHom (LargeScalar k) SY.tangent.evaluation)) (by omega))
      (dgClosedHom (LargeScalar k) (eqToHom (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k))) unit)))
      (by omega))
  coevaluation : HEq (dgClosedHom (LargeScalar k) pulledDual.coevaluation)
    (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
      (dgComp (LargeScalar k) (p := 0) (q := 0) (n := 0)
        (dgClosedHom (LargeScalar k) (eqToHom
          (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k))) unit.symm)))
        (pullback.functor.dgMap 0 (dgClosedHom (LargeScalar k) SY.tangent.coevaluation)) (by omega))
      (tensor.map SY.tangent.object SY.context.cotangent.object) (by omega))

variable {SX SY} {f : X ⟶ Y}

/-- The cotangent differential keeps the native source map and the exact source context. -/
def cotangentArrow (G : RelativeGeometry SX SY f) :
    DGHom (LargeScalar k) 0 (G.pullback.functor.obj SY.context.cotangent.object) SX.context.cotangent.object :=
  dgClosedHom (LargeScalar k)
    (dgClosedHomOf (LargeScalar k) G.source.differential.map G.source.differential.closed ≫
      eqToHom (congrArg (fun C => ForgetEnrichment.of (Cochains (LargeScalar k)) C.cotangent.object)
        G.context_eq))

/-- This same source differential is genuinely closed. -/
theorem cotangentArrow_closed (G : RelativeGeometry SX SY f) :
    cotangentArrow G ∈ dgCycles (LargeScalar k) _ _ := dgClosedHom_mem_dgCycles (LargeScalar k) _

/-- The actual tangent arrow is the native dual mate with the same pulled source pairing. -/
def tangentArrow (G : RelativeGeometry SX SY f) :
    DGHom (LargeScalar k) 0 SX.tangent.object (G.pullback.functor.obj SY.tangent.object) :=
  dgClosedHom (LargeScalar k)
    (dualDifferential SX.monoidal (cotangentArrow G) (cotangentArrow_closed G) SX.tangent G.pulledDual ≫
      eqToHom (congrArg (ForgetEnrichment.of (Cochains (LargeScalar k))) G.tangent_eq))

/-- Closure follows from the same native closed dual mate. -/
theorem tangentArrow_closed (G : RelativeGeometry SX SY f) :
    tangentArrow G ∈ dgCycles (LargeScalar k) _ _ := dgClosedHom_mem_dgCycles (LargeScalar k) _

/-- b is the actual pulled source Theta followed by the same cotangent differential df. -/
def sourceB (G : RelativeGeometry SX SY f) (n : ℤ) (ω : SourceClosedForm SY n) :
    DGHom (LargeScalar k) n (G.pullback.functor.obj SY.tangent.object) SX.context.cotangent.object :=
  dgComp (LargeScalar k) (p := n) (q := 0) (n := n)
    (G.pullback.functor.dgMap n (sourceTheta SY n ω)) (cotangentArrow G) (by omega)

/-- The literal b is closed by the native enriched map law and graded Leibniz rule. -/
theorem sourceB_closed (G : RelativeGeometry SX SY f) (n : ℤ) (ω : SourceClosedForm SY n) :
    dgDifferential (LargeScalar k) n (sourceB G n ω) = 0 := by
  rw [sourceB, dgDifferential_dgComp, ← G.pullback.functor.dgMap_dgDifferential,
    sourceTheta_closed, map_zero, (mem_dgCycles (LargeScalar k)).mp (cotangentArrow_closed G)]
  simp

/-- Pulling a homogeneous contraction uses the actual source DG functor, tangent mate and df. -/
def contractionHomPullback (G : RelativeGeometry SX SY f) :
    dgHomComplex (LargeScalar k) SY.tangent.object SY.context.cotangent.object ⟶
      dgHomComplex (LargeScalar k) SX.tangent.object SX.context.cotangent.object :=
  G.pullback.functor.map SY.tangent.object SY.context.cotangent.object ≫
    eHomWhiskerRight (Cochains (LargeScalar k))
      (dgClosedHomOf (LargeScalar k) (tangentArrow G) (tangentArrow_closed G))
      (ForgetEnrichment.of _ (G.pullback.functor.obj SY.context.cotangent.object)) ≫
    eHomWhiskerLeft (Cochains (LargeScalar k)) (ForgetEnrichment.of _ SX.tangent.object)
      (dgClosedHomOf (LargeScalar k) (cotangentArrow G) (cotangentArrow_closed G))

/-- Scalar transport keeps the same exact native source Hom complex on both sides. -/
def globalContractionHomPullback (G : RelativeGeometry SX SY f) :
    homGlobal SY.tangent.object SY.context.cotangent.object ⟶
      homGlobal SX.tangent.object SX.context.cotangent.object :=
  (coefficientsToGlobal k).map (contractionHomPullback G)

/-- The same pullback comparison is a full cochain homotopy between the two computed NC contraction maps.
It is constrained only by its boundary, so it is determined up to closed cochains; it is not pinned
to the comparison induced by the geometric pullback of forms. -/
structure ContractionPullbackHomotopy (G : RelativeGeometry SX SY f) where
  cochain : Cochain ((ncComplex SY.forms)⟦-2⟧)
    (homGlobal SX.tangent.object SX.context.cotangent.object) (-1)
  boundary : δ (-1) 0 cochain =
    Cochain.ofHom ((shiftFunctor (GlobalComplex k) (-2)).map (ncPullback f SY.forms SX.forms) ≫
      sourceContraction SX) -
    Cochain.ofHom (sourceContraction SY ≫ globalContractionHomPullback G)

/-- The source vertex is read in NC[-2] through the actual native shifts n-2 and -2+n. -/
def sourceNCVertex (n : ℤ) (ω : SourceClosedForm SY n) : ((ncComplex SY.forms)⟦-2⟧).X n :=
  vertexCoefficient ((ncComplex SY.forms)⟦-2⟧) n
    (((realize k).map ((shiftFunctorAdd' (GlobalComplex k) (-2 : ℤ) n (n - 2) (by omega)).hom.app
      (ncComplex SY.forms))).app (op ⦋0⦌) ω)

/-- The correction evaluates the same native pullback cochain on the actual NC vertex. -/
def pullbackCorrection {G : RelativeGeometry SX SY f} (C : ContractionPullbackHomotopy G)
    (n : ℤ) (ω : SourceClosedForm SY n) :
    DGHom (LargeScalar k) (n - 1) SX.tangent.object SX.context.cotangent.object :=
  (C.cochain.v n (n - 1) (by omega)).hom (sourceNCVertex n ω)

/-- h is the actual isotropic NC/DK coefficient minus that same computed comparison correction. -/
def sourceH {G : RelativeGeometry SX SY f} (C : ContractionPullbackHomotopy G)
    (n : ℤ) (ω : SourceClosedForm SY n)
    (h : IsotropicPath SX.forms n ((closedPullback f SY.forms SX.forms n).app (op ⦋0⦌) ω)) :
    DGHom (LargeScalar k) (n - 1) SX.tangent.object SX.context.cotangent.object :=
  sourceIsotropicHomotopy SX n ((closedPullback f SY.forms SX.forms n).app (op ⦋0⦌) ω) h -
    pullbackCorrection C n ω

/-- A witness records only the boundary proof for this fixed source path coefficient; its constructor is Wanted. -/
structure IsotropicBoundaryWitness {G : RelativeGeometry SX SY f} (C : ContractionPullbackHomotopy G)
    (n : ℤ) (ω : SourceClosedForm SY n)
    (h : IsotropicPath SX.forms n ((closedPullback f SY.forms SX.forms n).app (op ⦋0⦌) ω)) where
  boundary : dgDifferential (LargeScalar k) (n - 1) (sourceH C n ω h) =
    dgComp (LargeScalar k) (tangentArrow G) (sourceB G n ω) (by omega)

/-- The induced relative Theta is exactly i*h-c*b on the native represented cone[-1]. -/
def relativeTheta {G : RelativeGeometry SX SY f} (C : ContractionPullbackHomotopy G)
    (T : RelativeTangent (tangentArrow G) (tangentArrow_closed G))
    (n : ℤ) (ω : SourceClosedForm SY n)
    (h : IsotropicPath SX.forms n ((closedPullback f SY.forms SX.forms n).app (op ⦋0⦌) ω)) :
    DGHom (LargeScalar k) (n - 1) T.object SX.context.cotangent.object :=
  isotropicArrow T n (sourceB G n ω) (sourceH C n ω h)

/-- Closure uses the fixed isotropic boundary and the native mapping-cocone nullhomotopy. -/
theorem relativeTheta_closed {G : RelativeGeometry SX SY f} (C : ContractionPullbackHomotopy G)
    (T : RelativeTangent (tangentArrow G) (tangentArrow_closed G))
    (n : ℤ) (ω : SourceClosedForm SY n)
    (h : IsotropicPath SX.forms n ((closedPullback f SY.forms SX.forms n).app (op ⦋0⦌) ω))
    (W : IsotropicBoundaryWitness C n ω h) :
    dgDifferential (LargeScalar k) (n - 1) (relativeTheta C T n ω h) = 0 :=
  isotropicArrow_closed T n (sourceB G n ω) (sourceB_closed G n ω) (sourceH C n ω h) W.boundary

/-- Lagrangian nondegeneracy concerns this exact source-induced relative arrow, for the chosen
contraction pullback homotopy `C` and the chosen along representation of `G`: adding a closed
cochain to `C` changes the relative arrow, so this is the PTVV condition only for the geometric
choices. -/
def IsSourceLagrangian {G : RelativeGeometry SX SY f} (C : ContractionPullbackHomotopy G)
    (T : RelativeTangent (tangentArrow G) (tangentArrow_closed G))
    (n : ℤ) (ω : SourceClosedForm SY n)
    (h : IsotropicPath SX.forms n ((closedPullback f SY.forms SX.forms n).app (op ⦋0⦌) ω))
    (W : IsotropicBoundaryWitness C n ω h) : Prop :=
  IsShiftedEquivalence SX.context.cotangent.object T.object (n - 1) (relativeTheta C T n ω h)
    (relativeTheta_closed C T n ω h W)

end MathlibExt.AlgebraicGeometry.DerivedSourceRelativeIsotropicMaps
