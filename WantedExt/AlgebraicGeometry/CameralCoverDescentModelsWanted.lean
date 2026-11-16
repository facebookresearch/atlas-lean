/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralCoverDescentModels

/-!
# Native normalized incidence and cameral descent

These are direct construction/proof requests for the displayed actual
schemes, modules, torsors and normalized maps. Their definitions and
completed source ports remain in MathlibExt.
Source: DG arXiv:math/0005132v3, Sections 2, 7.1 and 17.1--17.5.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralCoverDescentModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels
open CameralRegularizedHiggsModels CameralCoverDescentModels CameralRamificationReindexing
open GroupTorsorGeometry
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

def_wanted nativeIncidenceAction (G : Over (Spec (.of ℂ))) [GrpObj G] [IsAffine G.left]
    [ConnectedSpace G.left] [Smooth G.hom] [LocallyOfFiniteType G.hom]
    (hRed : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) : IncidenceAction F

def_wanted nativeCoverDescent (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (P : Regularizer F X) : CoverDescent F I P

def_wanted nativeReindexCover (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X Y : Over (Spec (.of ℂ))) (P : Regularizer F X) (D : CoverDescent F I P) (f : Y ⟶ X)
    (r : GroupTorsorGeometry.Reindex G P.torsor f) : ReindexCover F I P D f r

end WantedExt.AlgebraicGeometry.CameralCoverDescentModelsWanted
