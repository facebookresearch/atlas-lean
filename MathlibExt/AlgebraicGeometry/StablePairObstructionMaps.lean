/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import MathlibExt.AlgebraicGeometry.StablePairParameterPullbacks
public import MathlibExt.AlgebraicGeometry.StablePairCotangentComparisons
public import MathlibExt.AlgebraicGeometry.StablePairProductCotangents
public import MathlibExt.AlgebraicGeometry.StablePairSerreMaps

/-!
# The geometric stable-pair obstruction-map composite

The universal truncated kernel, full-target lift, tensor action,
trace adjunction and trace-free inclusion are all attached to the
actual universal pair resolution. The cotangent projection uses
the full bar and product-refinement diagrams. The relative canonical
comparison is the native proper base-change mate.

Equation (2.13) is a public definition with its exact native source
and full cotangent target. A full-target lift is explicitly named as
a lift; its construction and compatibility with the source class are
separate proof work. Perfectness and the H⁰/H⁻¹ obstruction conditions
are also separate and are not fields of these map data.

References: Pandharipande–Thomas, arXiv:0707.2348v5, §2.3, (2.13);
Huybrechts–Thomas, arXiv:0805.3527v2, Definitions 2.3, 2.6,
§4.1–4.2, (4.2), and §4.5.
-/

set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section

namespace MathlibExt.AlgebraicGeometry.StablePairObstructionMaps

open CategoryTheory CategoryTheory.Limits
open _root_.AlgebraicGeometry
open FourierMukai CoherentCurveLinearSeries StablePairFamilies
open StablePairPerfectComplexes StablePairTraceModels StablePairTraceDualityModels
open StablePairDiagonalIdeals StablePairAtiyahKernels StablePairCochainTensorMaps
open StablePairFourierMukaiAtiyah StablePairCotangentComparisons
open StablePairProductCotangents StablePairCanonicalSources StablePairSerreMaps
open NormalizedModuleTensorMaps QuasicoherentDualityReferences ModuleDerivedSquares
open GlobalPerfectObstructionTheory
attribute [local instance] HasDerivedCategory.standard

variable [HasDerivedPullbacks.{0}] [HasDerivedPushforwards.{0}] [HasDerivedTensors.{0}]

/-- Only normalized kernel-construction dependencies, with no obstruction-theory conclusion. -/
structure UniversalKernelData (Y : Over (Spec (.of ℂ))) (K : Cochains Y.left) where
  ambient : Over (Spec (.of ℂ))
  embedding : Y ⟶ ambient
  [closed : IsClosedImmersion embedding.left]
  [smooth : Smooth ambient.hom]
  [separated : IsSeparated ambient.hom]
  [noetherian : IsNoetherian ambient.left]
  square : IdealSquare (diagonal ambient)
  augmentation : ResolutionAugmentation embedding
  projection : KernelProjection embedding square
  tensor : PullbackTensor (diagonal Y)
  pasting : PushforwardPasting (diagonal Y) (pullback.snd Y.hom Y.hom)
  identity : PushforwardIdentity Y.left
  unit : RightUnitCochainMap Y K
  diagonalUnit : DiagonalCochainMap Y tensor K (unitComplex Y)
  diagonalTruncated : DiagonalCochainMap Y tensor K ((cotangent embedding square)⟦(1 : ℤ)⟧)
  unitPushIso : IsIso ((derivedPushforwardUnit (diagonal Y)).app (unitComplex Y))
  truncatedPushIso : IsIso
    ((derivedPushforwardUnit (diagonal Y)).app ((cotangent embedding square)⟦(1 : ℤ)⟧))
  unitTensorIso : IsIso (tensorCounit Y.left K (unitComplex Y))
  truncatedTensorIso : IsIso (tensorCounit Y.left K ((cotangent embedding square)⟦(1 : ℤ)⟧))
  targetPushIso : IsIso (targetPushMap embedding square)
  identityIso : IsIso (identityKernelMap Y K tensor diagonalUnit unit pasting identity
    unitPushIso unitTensorIso)

variable {Y : Over (Spec (.of ℂ))} {K : Cochains Y.left}

/-- The concrete truncated kernel action associated to those dependencies. -/
def truncatedClass (D : UniversalKernelData Y K) :
    DerivedCategory.Q.obj K ⟶ (derivedTensorUncurried Y.left).obj
      (DerivedCategory.Q.obj K,
        DerivedCategory.Q.obj ((cotangent D.embedding D.square)⟦(1 : ℤ)⟧)) :=
  truncatedAtiyah Y D.embedding D.square D.augmentation D.projection K D.tensor
    D.diagonalUnit D.unit D.diagonalTruncated D.pasting D.identity
    D.unitPushIso D.truncatedPushIso D.unitTensorIso D.truncatedTensorIso
    D.targetPushIso D.identityIso

/-- A full universal-kernel lift with its projection fixed to the actual truncated diagram.
This type does not label an arbitrary compatible lift canonical. -/
structure FullKernelLift (D : UniversalKernelData Y K) (C : CotangentNormalization Y.hom)
    (Q : CotangentTruncation D.embedding D.square C) where
  map : DerivedCategory.Q.obj
    ((CochainComplex.singleFunctor (pullback Y.hom Y.hom).Modules 0).obj
      ((Scheme.Modules.pushforward (diagonal Y)).obj (structureModule Y.left))) ⟶
    (derivedPushforward (diagonal Y)).obj (DerivedCategory.Q.obj (C.complex⟦(1 : ℤ)⟧))
  projection_compatibility : map ≫
    (derivedPushforward (diagonal Y)).map (DerivedCategory.Q.map (Q.projection⟦(1 : ℤ)⟧')) =
      universalClass D.embedding D.square D.augmentation D.projection D.targetPushIso
  diagonalMap : DiagonalCochainMap Y D.tensor K (C.complex⟦(1 : ℤ)⟧)
  pushIso : IsIso ((derivedPushforwardUnit (diagonal Y)).app (C.complex⟦(1 : ℤ)⟧))
  tensorIso : IsIso (tensorCounit Y.left K (C.complex⟦(1 : ℤ)⟧))

/-- Apply the full universal-kernel lift by the same actual Fourier–Mukai operators. -/
def fullClass (D : UniversalKernelData Y K) (C : CotangentNormalization Y.hom)
    (Q : CotangentTruncation D.embedding D.square C) (L : FullKernelLift D C Q) :
    DerivedCategory.Q.obj K ⟶ (derivedTensorUncurried Y.left).obj
      (DerivedCategory.Q.obj K,DerivedCategory.Q.obj (C.complex⟦(1 : ℤ)⟧)) := by
  letI := D.identityIso
  exact inv (identityKernelMap Y K D.tensor D.diagonalUnit D.unit D.pasting D.identity
      D.unitPushIso D.unitTensorIso) ≫
    kernelMap Y L.map (DerivedCategory.Q.obj K) ≫
      diagonalTensorMap Y K (C.complex⟦(1 : ℤ)⟧) D.tensor L.diagonalMap D.pasting D.identity
        L.pushIso L.tensorIso

/-- Native cancellation of the shifts used when the degree-one class is transposed. -/
def cancelOneShift {V : Scheme} (L : Cochains V) : (L⟦(1 : ℤ)⟧)⟦(-1 : ℤ)⟧ ≅ L :=
  ((CochainComplex.shiftFunctorAdd' V.Modules 1 (-1) 0 (by omega)).app L).symm ≪≫
    (CochainComplex.shiftFunctorZero' V.Modules 0 rfl).app L

/-- Move a degree-one class down by the actual shift/localization comparisons. -/
def classShiftDown {V : Scheme} (A B : Cochains V)
    (a : DerivedCategory.Q.obj A ⟶ DerivedCategory.Q.obj (B⟦(1 : ℤ)⟧)) :
    DerivedCategory.Q.obj (A⟦(-1 : ℤ)⟧) ⟶ DerivedCategory.Q.obj B :=
  (DerivedCategory.Q.commShiftIso (-1 : ℤ)).hom.app A ≫ a⟦(-1 : ℤ)⟧' ≫
    (DerivedCategory.Q.commShiftIso (-1 : ℤ)).inv.app (B⟦(1 : ℤ)⟧) ≫
      DerivedCategory.Q.map (cancelOneShift B).hom

variable (X P : Over (Spec (.of ℂ))) (F : RawPair X P)
  (A : PairResolution F) (he : EndSquaredZero A.toFiniteComplex)
  (hd : DualSquaredZero A.toFiniteComplex) (T : TracePacket A.toFiniteComplex he)

/-- The actual degree-one trace-free class from the native trace adjunction. -/
def traceFreeClass
    (V : TraceFreeInclusion A.toFiniteComplex T)
    (H : EndTensorComparison A.toFiniteComplex hd he)
    (J : PerfectTensorAdjunction A.toFiniteComplex hd)
    (ht : IsIso (tensorCounit (total X P) (dualComplex A.toFiniteComplex hd) A.cochain))
    (D : UniversalKernelData (product X P) A.cochain)
    (C : CotangentNormalization (product X P).hom)
    (Q : CotangentTruncation D.embedding D.square C) (L : FullKernelLift D C Q) :
    traceFreeDerived A.toFiniteComplex T ⟶ DerivedCategory.Q.obj (C.complex⟦(1 : ℤ)⟧) :=
  DerivedCategory.Q.map V.map ≫
    traceMate A.toFiniteComplex hd he H J (C.complex⟦(1 : ℤ)⟧) ht (fullClass D C Q L)

variable (PX : ProperReference X.hom) (PP : ProperReference (projection X P))

/-- The actual inputs to the canonical product base-change map. -/
structure CanonicalProductData where
  model : CanonicalModel PX
  xAdjunction : PullPushAdjunction X.hom
  pAdjunction : PullPushAdjunction (projection X P)
  pPasting : PullbackPasting (projection X P) P.hom
  xPasting : PullbackPasting (pullback.fst X.hom P.hom) X.hom
  unit : UnitPullback P.hom
  quasicoherent : FourierMukai.quasicoherent (total X P)
    ((derivedPullback (pullback.fst X.hom P.hom)).obj (properDuality PX))
  baseChangeIso : IsIso (ModuleDerivedSquares.baseChangeMap (pullback.fst X.hom P.hom)
    (projection X P) X.hom P.hom pullback.condition xAdjunction pAdjunction pPasting xPasting
    (properDuality PX))
  pullbackIso : IsIso (pullbackCounit (pullback.fst X.hom P.hom)
    (((CochainComplex.singleFunctor X.left.Modules 0).obj
      (properCanonicalModule PX 3))⟦(3 : ℤ)⟧))

/-- No relative canonical map is supplied: it is computed from native proper base change. -/
def canonicalComparison (D : CanonicalProductData X P PX) :
    DerivedCategory.Q.obj ((omegaComplex X P PX)⟦(3 : ℤ)⟧) ⟶ properDuality PP :=
  relativeCanonicalMap X P PX PP D.model D.xAdjunction D.pAdjunction D.pPasting D.xPasting
    D.unit D.quasicoherent D.baseChangeIso D.pullbackIso

/-- Exactly the trace-free source displayed in equation (2.13). -/
def obstructionSource : D P.left :=
  ((derivedPushforward (projection X P)).obj
    ((derivedTensorUncurried (total X P)).obj
      (traceFreeDerived A.toFiniteComplex T,DerivedCategory.Q.obj (omegaComplex X P PX))))⟦(2 : ℤ)⟧

/-- Equation (2.13), assembled from the actual universal kernel and the native Serre adjunction. -/
def obstructionMap
    (V : TraceFreeInclusion A.toFiniteComplex T)
    (H : EndTensorComparison A.toFiniteComplex hd he)
    (J : PerfectTensorAdjunction A.toFiniteComplex hd)
    (ht : IsIso (tensorCounit (total X P) (dualComplex A.toFiniteComplex hd) A.cochain))
    (D : UniversalKernelData (product X P) A.cochain)
    (C : CotangentNormalization (product X P).hom)
    (R : CotangentNormalization (pullback.fst X.hom P.hom))
    (B : CotangentNormalization P.hom)
    (Q : CotangentTruncation D.embedding D.square C) (L : FullKernelLift D C Q)
    (G : ProductCotangentDiagram X P C R B)
    (hBase : IsIso (DerivedCategory.Q.map (G.baseChange⟦(1 : ℤ)⟧')))
    (hPull : IsIso (pullbackCounit (projection X P) B.complex))
    (N : CanonicalProductData X P PX)
    (S : CochainTwistShiftMap (traceFreeComplex A.toFiniteComplex T) (omegaModule X P PX))
    (hTwist : IsIso (tensorCounit (total X P) ((omegaComplex X P PX)⟦(3 : ℤ)⟧)
      ((traceFreeComplex A.toFiniteComplex T)⟦(-1 : ℤ)⟧)))
    (PS : PushforwardShift (projection X P))
    (TP : PullbackTensor (projection X P)) (PF : DerivedProjectionFormula (projection X P) TP)
    (U : LeftUnitCochainMap B.complex)
    (hPF : IsIso (PF.map (DerivedCategory.Q.obj ((omegaComplex X P PX)⟦(3 : ℤ)⟧))
      (DerivedCategory.Q.obj B.complex)))
    (hSerre : quasicoherent (total X P) ((derivedTensorUncurried (total X P)).obj
      (DerivedCategory.Q.obj ((omegaComplex X P PX)⟦(3 : ℤ)⟧),
        (derivedPullback (projection X P)).obj (DerivedCategory.Q.obj B.complex))))
    (hTarget : quasicoherent P.left (DerivedCategory.Q.obj B.complex)) :
    obstructionSource X P F A he T PX ⟶ DerivedCategory.Q.obj B.complex := by
  letI := PP.adjoint
  letI := PS.shift
  letI := hPull
  let a := traceFreeClass X P F A he hd T V H J ht D C Q L ≫
    productProjectionCochain X P C R B G 1 hBase
  let b := classShiftDown (traceFreeComplex A.toFiniteComplex T)
    ((cochainParameterPullback X P).obj B.complex) a ≫
      inv (pullbackCounit (projection X P) B.complex)
  let w := canonicalComparison X P PX PP N
  let s := serreCoefficient PP ((omegaComplex X P PX)⟦(3 : ℤ)⟧) w B.complex TP PF U
    hPF hSerre hTarget
  dsimp only [omegaComplex] at s
  let tensorB := (derivedTensorUncurried (total X P)).map
    (X := (DerivedCategory.Q.obj
        (((CochainComplex.singleFunctor (total X P).Modules 0).obj
          (omegaModule X P PX))⟦(3 : ℤ)⟧),
      DerivedCategory.Q.obj ((traceFreeComplex A.toFiniteComplex T)⟦(-1 : ℤ)⟧)))
    (Y := (DerivedCategory.Q.obj
        (((CochainComplex.singleFunctor (total X P).Modules 0).obj
          (omegaModule X P PX))⟦(3 : ℤ)⟧),
      (derivedPullback (projection X P)).obj (DerivedCategory.Q.obj B.complex)))
    (𝟙 _,b)
  exact ((derivedPushforward (projection X P)).commShiftIso (2 : ℤ)).inv.app
      ((derivedTensorUncurried (total X P)).obj
        (traceFreeDerived A.toFiniteComplex T,DerivedCategory.Q.obj (omegaComplex X P PX))) ≫
    (derivedPushforward (projection X P)).map
      (twistShiftMap (traceFreeComplex A.toFiniteComplex T) (omegaModule X P PX) S hTwist) ≫
    (derivedPushforward (projection X P)).map tensorB ≫
    (derivedPushforward (projection X P)).map s ≫
      ((Adjunction.ofIsLeftAdjoint (directImage (projection X P) PP.preservation)).counit.app
        (⟨DerivedCategory.Q.obj B.complex,hTarget⟩ : QCohDerived P.left)).hom

/-- A reviewable packet of actual source objects and normalized construction dependencies.
It contains no perfectness or obstruction-theory homology conclusion. -/
structure MapConstruction (X P : Over (Spec (.of ℂ))) (F : Family X P) where
  resolution : PairResolution F.toRawPair
  endSquaredZero : EndSquaredZero resolution.toFiniteComplex
  dualSquaredZero : DualSquaredZero resolution.toFiniteComplex
  trace : TracePacket resolution.toFiniteComplex endSquaredZero
  traceInclusion : TraceFreeInclusion resolution.toFiniteComplex trace
  endTensor : EndTensorComparison resolution.toFiniteComplex dualSquaredZero endSquaredZero
  tensorAdjunction : PerfectTensorAdjunction resolution.toFiniteComplex dualSquaredZero
  endTensorIso : IsIso (tensorCounit (total X P)
    (dualComplex resolution.toFiniteComplex dualSquaredZero) resolution.cochain)
  kernel : UniversalKernelData (product X P) resolution.cochain
  productCotangent : CotangentNormalization (product X P).hom
  relativeCotangent : CotangentNormalization (pullback.fst X.hom P.hom)
  parameterCotangent : CotangentNormalization P.hom
  truncation : CotangentTruncation kernel.embedding kernel.square productCotangent
  fullLift : FullKernelLift kernel productCotangent truncation
  cotangentDiagram :
    ProductCotangentDiagram X P productCotangent relativeCotangent parameterCotangent
  cotangentBaseChangeIso : IsIso (DerivedCategory.Q.map (cotangentDiagram.baseChange⟦(1 : ℤ)⟧'))
  parameterPullbackIso : IsIso (pullbackCounit (projection X P) parameterCotangent.complex)
  xProper : ProperReference X.hom
  pProper : ProperReference (projection X P)
  canonical : CanonicalProductData X P xProper
  twistShift : CochainTwistShiftMap (traceFreeComplex resolution.toFiniteComplex trace)
    (omegaModule X P xProper)
  twistTensorIso : IsIso (tensorCounit (total X P) ((omegaComplex X P xProper)⟦(3 : ℤ)⟧)
    ((traceFreeComplex resolution.toFiniteComplex trace)⟦(-1 : ℤ)⟧))
  pushforwardShift : PushforwardShift (projection X P)
  pullbackTensor : PullbackTensor (projection X P)
  projectionFormula : DerivedProjectionFormula (projection X P) pullbackTensor
  leftUnit : LeftUnitCochainMap parameterCotangent.complex
  projectionFormulaIso : IsIso
    (projectionFormula.map (DerivedCategory.Q.obj ((omegaComplex X P xProper)⟦(3 : ℤ)⟧))
      (DerivedCategory.Q.obj parameterCotangent.complex))
  serreSource : quasicoherent (total X P) ((derivedTensorUncurried (total X P)).obj
    (DerivedCategory.Q.obj ((omegaComplex X P xProper)⟦(3 : ℤ)⟧),
      (derivedPullback (projection X P)).obj (DerivedCategory.Q.obj parameterCotangent.complex)))
  target : quasicoherent P.left (DerivedCategory.Q.obj parameterCotangent.complex)

namespace MapConstruction
variable {X P : Over (Spec (.of ℂ))} {F : Family X P} (M : MapConstruction X P F)

/-- The source is the same fixed trace-free pushforward and degree-two shift. -/
def source : D P.left :=
  obstructionSource X P F.toRawPair M.resolution M.endSquaredZero M.trace M.xProper

/-- The assembled map is exactly the public equation (2.13) composite. -/
def map : M.source ⟶ DerivedCategory.Q.obj M.parameterCotangent.complex :=
  obstructionMap X P F.toRawPair M.resolution M.endSquaredZero M.dualSquaredZero M.trace
    M.xProper M.pProper M.traceInclusion M.endTensor M.tensorAdjunction M.endTensorIso M.kernel
    M.productCotangent M.relativeCotangent M.parameterCotangent M.truncation M.fullLift
    M.cotangentDiagram M.cotangentBaseChangeIso M.parameterPullbackIso M.canonical M.twistShift
    M.twistTensorIso M.pushforwardShift M.pullbackTensor M.projectionFormula M.leftUnit
    M.projectionFormulaIso M.serreSource M.target
end MapConstruction

end MathlibExt.AlgebraicGeometry.StablePairObstructionMaps
