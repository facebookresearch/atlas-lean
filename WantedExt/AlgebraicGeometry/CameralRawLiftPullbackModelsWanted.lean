/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralRawLiftPullbackModels

/-!
# Native all-base Borel quotient comparisons

The comparison fixes the original torsor, cameral map and every B-to-T
quotient point. The parameter comparison fixes both product factors.
Source: DG math/0005132v3, Sections7/16.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralRawLiftPullbackModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralCoverDescentModels CameralBorelReductionModels
open CameralBorelAbelianizationCore CameralRawLiftPullbackModels ExpansionParameterModels
open CameralNormalizerShifts

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] torusGroup
attribute [local instance] borelGroup
attribute [local instance] quotientHom

def_wanted nativeBorelTorusPullback (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [GeneralLinearFrameSchemes.FrameTheory 2]
    [RankTwoMatrixGroupModels.GL2MatrixTheory] [RankTwoMatrixGroupModels.SL2MatrixTheory]
    (K : RootNormalizerGeometry G tori F) (D : RootTorsorInputs F K)
    (I : IncidenceAction F) (B : BorelGeometry F) (X Y : Over (Spec (.of ℂ)))
    (C : Cover F X) (C' : Cover F Y) (m : CameralArrow F C C')
    (H : Marked F I C) (H' : Marked F I C') (a : RegularizerAlong F I m H H')
    (N : ReductionFamily F B I C) (N' : ReductionFamily F B I C')
    (O : BorelTorusOperations F B) : BorelTorusPullback F K D I B m H H' a N N' O

def_wanted nativeParameterAlong (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X Y : Over (Spec (.of ℂ))) (C : Cover F X) (C' : Cover F Y) (m : CameralArrow F C C')
    (B : ParameterCovers F C) (B' : ParameterCovers F C') : ParameterAlong F m B B'

end WantedExt.AlgebraicGeometry.CameralRawLiftPullbackModelsWanted
