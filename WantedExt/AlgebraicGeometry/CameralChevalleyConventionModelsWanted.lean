/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralChevalleyConventionModels

/-!
# The actual pinned G and N convention comparison

These are direct construction/proof requests for the displayed actual
schemes, modules, torsors and normalized maps. Their definitions and
completed source ports remain in MathlibExt.
Source: DG arXiv:math/0005132v3, Sections 6--8 and 15--16; pinned Chevalley involution.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralChevalleyConventionModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels
open CameralRootSL2Sources CameralChevalleyConventionModels GeneralLinearFrameSchemes
open RankTwoMatrixGroupModels

def_wanted nativeChevalleyComparison (G : Over (Spec (.of ℂ))) [GrpObj G] [IsAffine G.left]
    [ConnectedSpace G.left] [Smooth G.hom] [LocallyOfFiniteType G.hom]
    (hRed : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F) :
    ChevalleyComparison F K

end WantedExt.AlgebraicGeometry.CameralChevalleyConventionModelsWanted
