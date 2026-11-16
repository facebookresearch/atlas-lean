/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralUnramifiedNormalizerModels

/-!
# Actual Cartan-fibre N reductions

These are direct construction/proof requests for the displayed actual
schemes, modules, torsors and normalized maps. Their definitions and
completed source ports remain in MathlibExt.
Source: DG arXiv:math/0005132v3, Sections 7.2 and 8.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralUnramifiedNormalizerModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels
open CameralRegularizedHiggsModels CameralCoverDescentModels CameralBorelReductionModels
open CameralBorelAbelianizationCore CameralUnramifiedNormalizerModels CameralRamificationReindexing
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] CameralBorelReductionModels.borelGroup
attribute [local instance] CameralBorelReductionModels.quotientHom
attribute [local instance] CameralUnramifiedNormalizerModels.normalizerGroup

def_wanted nativeCartanPoint (G : Over (Spec (.of ℂ))) [GrpObj G] [IsAffine G.left]
    [ConnectedSpace G.left] [Smooth G.hom] [LocallyOfFiniteType G.hom]
    (hRed : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) : CartanPoint F

def_wanted nativeNormalizerReduction (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) [Etale C.cover.scheme.hom]
    (H : CameralMarkedRegularizers.Object F I C) (Z : CartanPoint F) : NormalizerReduction F I C H Z

def_wanted nativeTorusNormalizerCover (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) (H : CameralMarkedRegularizers.Object F I C)
    (Z : CartanPoint F) (N : NormalizerReduction F I C H Z) : TorusNormalizerCover F I C H Z N

def_wanted nativeBorelNormalizerComparison (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (B : BorelGeometry F)
    (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) (H : CameralMarkedRegularizers.Object F I C)
    (Z : CartanPoint F) (N : NormalizerReduction F I C H Z) (T : TorusNormalizerCover F I C H Z N)
    (R : ReductionFamily F B I C) (O : BorelTorusOperations F B) :
    BorelNormalizerComparison F B I C H Z N R O T

end WantedExt.AlgebraicGeometry.CameralUnramifiedNormalizerModelsWanted
