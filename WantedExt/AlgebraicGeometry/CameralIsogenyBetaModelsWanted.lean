/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralIsogenyBetaModels

/-!
# Canonical beta construction through the actual central cover

The source constructor chooses an actual pinned central group isogeny
with primitive coroots and every quotient-point/dual-line comparison.
It supplies the canonical universal raw data, including beta on the
ramification scheme. No compatible beta is an independent input.
Source: DG math/0005132v3, Section7.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralIsogenyBetaModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationCocycles CameralCharacterRealizations
open CameralSimpleRootTrivializations CameralLiftedNormalizerModels
open CameralCoverDescentModels CameralBorelReductionModels ExpansionParameterModels
open CameralUniversalRegularizerModels CameralUniversalRawLiftModels CameralIsogenyBetaModels

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

def_wanted nativePrimitiveCentralSource (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [GeneralLinearFrameSchemes.FrameTheory 2]
    [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
    (K : RootNormalizerGeometry G tori F) (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (I : IncidenceAction F) (B : BorelGeometry F) : PrimitiveSource F K I B

def_wanted nativeNormalizedUniversalRaw (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [GeneralLinearFrameSchemes.FrameTheory 2]
    [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
    (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
    (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
    (Q : SimpleReflectionTorsors F K D R) (E : RootWeylGeometry F K)
    (T : CanonicalSimpleRootTrivializations F K D R A)
    (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (I : IncidenceAction F) (B : BorelGeometry F) (V : LiftInputs F I B)
    (U : UniversalRegularizer F I) : NormalizedUniversal F K D R A Q E T I B V U

end WantedExt.AlgebraicGeometry.CameralIsogenyBetaModelsWanted
