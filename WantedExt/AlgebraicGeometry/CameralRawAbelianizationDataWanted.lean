/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralRawAbelianizationData

/-!
# Transport of the raw gamma and beta conventions

These are direct construction/proof requests for the displayed actual
schemes, modules, torsors and normalized maps. Their definitions and
completed source ports remain in MathlibExt.
Source: DG arXiv:math/0005132v3, Sections 6--8 and 15--16.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralRawAbelianizationDataWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels
open CameralRootSL2Sources CameralRamificationTensorModels CameralRamificationReindexing
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open CameralLiftedNormalizerModels CameralNormalizerShifts CameralChevalleyConventionModels
open CameralRawAbelianizationData ContractedTorsorModels
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels
attribute [local instance] CameralRamificationTensorModels.torusGroup

def_wanted nativeConventionAdaptation (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) (R : CanonicalRamificationFamily F K D) (A : CharacterCalculus F K D)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) (P : ParameterCovers F C)
    (L : Bundle (Torus F) (total F C)) (β : RawBetaMaps F K D R A P L)
    (S : RawNormalizerShift F K D R P L) (Q : SimpleReflectionTorsors F K D R)
    (E : RootWeylGeometry F K) (T : CanonicalSimpleRootTrivializations F K D R A)
    (Θ : ChevalleyComparison F K) (J : RawBetaCompatibility F K D R A P L β S Q E T) :
    AdaptedRamificationData F K D R A P L β S Q E T Θ J

end WantedExt.AlgebraicGeometry.CameralRawAbelianizationDataWanted
