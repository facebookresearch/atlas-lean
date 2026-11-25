/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralBorelReductionModels

/-!
# The actual Borel group and torus reduction

These are direct construction/proof requests for the displayed actual
schemes, modules, torsors and normalized maps. Their definitions and
completed source ports remain in MathlibExt.
Source: DG arXiv:math/0005132v3, Sections 7.2 and 16.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralBorelReductionModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels
open CameralRegularizedHiggsModels CameralCoverDescentModels CameralBorelReductionModels
open CameralRamificationReindexing
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction
attribute [local instance] CameralBorelReductionModels.borelGroup
attribute [local instance] CameralBorelReductionModels.quotientHom
attribute [local instance] CameralRamificationTensorModels.torusGroup

def_wanted nativeBorelGeometry (G : Over (Spec (.of ℂ))) [GrpObj G] [IsAffine G.left]
    [ConnectedSpace G.left] [Smooth G.hom] [LocallyOfFiniteType G.hom]
    (hRed : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) : BorelGeometry F

def_wanted nativeBorelTorusOperations (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (B : BorelGeometry F) : BorelTorusOperations F B

def_wanted nativeBorelReduction (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (B : BorelGeometry F)
    (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (P : Regularizer F X)
    (D : CoverDescent F I P) : BorelReduction F B I P D

end WantedExt.AlgebraicGeometry.CameralBorelReductionModelsWanted
