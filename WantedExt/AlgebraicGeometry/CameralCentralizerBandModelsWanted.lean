/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralCentralizerBandModels

/-!
# Actual centralizer-group and cameral-band comparison

The group fixes every native coefficient of the actual regular
centralizer plane. Its comparison to the band uses the actual Borel
conjugation and B-to-T quotient on every affine incidence chart.
Source: DG arXiv:math/0005132v3, Sections 11--12 and Theorem 4.4.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralCentralizerBandModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels CameralCoverDescentModels
open CameralBorelReductionModels CameralCentralizerBandModels
attribute [local instance] CameralCentralizerBandModels.centralizerGroup
attribute [local instance] CameralCentralizerBandModels.universalBandGroup

def_wanted nativeCentralizerGroup (G : Over (Spec (.of ℂ))) [GrpObj G] [IsAffine G.left]
    [ConnectedSpace G.left] [Smooth G.hom] [LocallyOfFiniteType G.hom]
    (hRed : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) : CentralizerGroup F

def_wanted nativeUniversalBandComparison (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (B : BorelGeometry F) (I : IncidenceAction F) (J : CentralizerGroup F) :
    UniversalBandComparison F B I J

end WantedExt.AlgebraicGeometry.CameralCentralizerBandModelsWanted
