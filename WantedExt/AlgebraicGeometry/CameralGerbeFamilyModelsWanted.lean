/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralGerbeFamilyModels

/-!
# Actual cameral family restrictions and local banded gerbe

All constructors use native torsor/cover pullbacks and normalized
original maps. The local gerbe, automorphism bijection and restriction
compatibility are direct conclusions on those same actual maps.
Source: DG math/0005132v3, Theorem4.4/Corollary4.6/Sections14/16.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralGerbeFamilyModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralCoverDescentModels CameralRamificationReindexing
open CameralBorelReductionModels CameralCentralizerBandModels CameralGerbeFamilyModels
open ExpansionParameterModels

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

def_wanted nativeMarkedFamilies (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) : MarkedFamilies F I C

def_wanted nativeLocalAutomorphisms (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (I : IncidenceAction F) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (M : MarkedFamilies F I C) (B : BorelGeometry F) (J : CentralizerGroup F) :
    LocalAutomorphisms F I C M B J

def_wanted nativeLocalBandRestriction (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (I : IncidenceAction F) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (M : MarkedFamilies F I C) : LocalBandRestriction F I C M

theorem_wanted nativeLocalBandRestrictionLaws (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (I : IncidenceAction F) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (M : MarkedFamilies F I C) (L : LocalBandRestriction F I C M) : BandRestrictionLaws F I C M L

theorem_wanted nativeLocalAutomorphismRestriction (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (I : IncidenceAction F) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (M : MarkedFamilies F I C) (B : BorelGeometry F) (J : CentralizerGroup F)
    (L : LocalBandRestriction F I C M) (A : LocalAutomorphisms F I C M B J) :
    AutomorphismRestriction F I C M B J L A

def_wanted nativeBandedIsomTorsor (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (I : IncidenceAction F) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (M : MarkedFamilies F I C) (B : BorelGeometry F) (J : CentralizerGroup F)
    (L : LocalBandRestriction F I C M) (A : LocalAutomorphisms F I C M B J)
    (U : Over X.left)
    (H H' : CameralBorelAbelianizationCore.Marked F I (M.cover U).cover) :
    BandedIsomTorsor F I C M B J L A U H H'

theorem_wanted nativeAutomorphismBijection (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (I : IncidenceAction F) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (M : MarkedFamilies F I C) (B : BorelGeometry F) (J : CentralizerGroup F)
    (A : LocalAutomorphisms F I C M B J) (U : Over X.left)
    (H : CameralBorelAbelianizationCore.Marked F I (M.cover U).cover) :
    Function.Bijective (A.source U H).arrow

/-- The étale-local part of Donagi–Gaitsgory, Thm. 4.4: marked objects exist étale locally
and are étale locally isomorphic. -/
theorem_wanted nativeLocalGerbe (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (I : IncidenceAction F) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (M : MarkedFamilies F I C) : LocalGerbe F I C M

end WantedExt.AlgebraicGeometry.CameralGerbeFamilyModelsWanted
