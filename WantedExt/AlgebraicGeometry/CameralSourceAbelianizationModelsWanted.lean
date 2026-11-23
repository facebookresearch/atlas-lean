/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralSourceAbelianizationModels

/-!
# Source Borel construction and its actual fibre equivalences

The universal beta is fixed through the actual primitive central cover.
The all-family constructor fixes every original Borel/parameter map.
Both source equivalence requests target the computed functors.
Source: DG math/0005132v3, Theorems6.4/17.5 and Corollary17.8.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralSourceAbelianizationModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationCocycles CameralCharacterRealizations
open CameralSimpleRootTrivializations CameralLiftedNormalizerModels
open CameralCoverDescentModels CameralBorelReductionModels ExpansionParameterModels
open CameralUniversalRegularizerModels CameralUniversalRawLiftModels CameralIsogenyBetaModels
open CameralSourceAbelianizationModels CameralRegularizedHiggsModels
open CameralHiggsCategoryModels CameralCartanValueModels CameralHitchinFunctorModels

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

variable (G : Over (Spec (.of ℂ))) [GrpObj G]
  (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
  [GeneralLinearFrameSchemes.FrameTheory 2]
  [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
  (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
  (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
  (Q : SimpleReflectionTorsors F K D R) (E : RootWeylGeometry F K)
  (T : CanonicalSimpleRootTrivializations F K D R A)
  (I : IncidenceAction F) (B : BorelGeometry F) (V : LiftInputs F I B)
  (U : UniversalRegularizer F I) (W : NormalizedUniversal F K D R A Q E T I B V U)

def_wanted nativeSourceLiftInputs (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G) :
    LiftInputs F I B

def_wanted nativeAllFamilyRaw (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G) :
    AllFamilyRawConstruction F K D R A Q E T I B V U W.raw

def_wanted nativeSourceAbelianization (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G) :
    SourceConstruction F K D R A Q E T I B V U W

variable (S : SourceConstruction F K D R A Q E T I B V U W)

theorem_wanted nativeBorelFunctorEquivalence (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) :
    (borelFunctor F K D R A Q E T I B V U W S C).IsEquivalence

theorem_wanted nativeRegularizedValueFibreEquivalence
    (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (X : Over (Spec (.of ℂ))) (L : TwistLine X)
    (Space : SectionSpace X (cartanKModule F X L)) (Action : CartanWeylAction F X L Space)
    (Coherence : CategoryCoherence F (X := X) (K := L)) (b : ValueObject F L Space Action)
    (P : FibreArrowCoherence F I L Space Action b) :
    letI := fibreCategory F I L Space Action Coherence b
    (regularizedFibreFunctor F K D R A Q E T I B V U W S L Space Action Coherence b P).IsEquivalence

end WantedExt.AlgebraicGeometry.CameralSourceAbelianizationModelsWanted
