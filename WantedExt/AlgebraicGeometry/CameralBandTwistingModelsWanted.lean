/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralBandTwistingModels

/-!
# Native band action, contracted twisting and H1 source theorems

These requests target the computed universal-centralizer action and
the actual inverse-diagonal fppf quotient. Unit/tensor/inverse arrows
are normalized before passing to actual torsor isomorphism classes.
The simple-transitivity theorem has an actual chosen fibre object.
Source: DG math/0005132v3, Theorem4.4/Corollary4.6/Sections14/16.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralBandTwistingModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralCoverDescentModels CameralRamificationReindexing
open CameralBorelReductionModels CameralCentralizerBandModels CameralBandPullbackModels
open CameralBandTwistingModels ExpansionParameterModels

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] bandGroup

def_wanted nativeBandAction (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (I : IncidenceAction F) (B : BorelGeometry F) (J : CentralizerGroup F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) (H : Marked F I C)
    (V : BandPullbackComparison F I B J C H) : BandAction F I B J C H V

def_wanted nativeBandTorsorOperations (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) : BandTorsorOperations F C

def_wanted nativeTwistingGeometry (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (I : IncidenceAction F) (B : BorelGeometry F) (J : CentralizerGroup F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) : TwistingGeometry F I B J C

def_wanted nativeTwistingQuotientCoherence (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (I : IncidenceAction F) (B : BorelGeometry F) (J : CentralizerGroup F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) (O : BandTorsorOperations F C)
    (T : TwistingGeometry F I B J C) : QuotientCoherence F I B J C O T

theorem_wanted nativeH1GroupLaws (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) (O : BandTorsorOperations F C) : H1GroupLaws F C O

theorem_wanted nativeTwistingClassCoherence (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (I : IncidenceAction F) (B : BorelGeometry F) (J : CentralizerGroup F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) (O : BandTorsorOperations F C)
    (T : TwistingGeometry F I B J C) (A : QuotientCoherence F I B J C O T) :
    TwistingCoherence F I B J C O T

theorem_wanted nativeH1SimplyTransitive (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (I : IncidenceAction F) (B : BorelGeometry F) (J : CentralizerGroup F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) (T : TwistingGeometry F I B J C)
    (H : Marked F I C) : SimplyTransitiveFrom F I B J C T H

end WantedExt.AlgebraicGeometry.CameralBandTwistingModelsWanted
