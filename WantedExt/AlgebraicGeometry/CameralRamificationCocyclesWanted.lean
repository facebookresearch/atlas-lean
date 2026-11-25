/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralRamificationCocycles

/-!
# The source canonical ramification cocycle construction

The output has the actual R_(u*v)->v*R_u tensor R_v map, complete
cocycle, universal polynomial/dense-open normalization and actual
all-coefficient Cartesian cameral pullback diagrams. No density is
assumed of arbitrary cameral fibres.
Source: DG arXiv:math/0005132v3, Lemma 5.4 and Proposition 5.5.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralRamificationCocyclesWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationTensorModels
open CameralRamificationCocycles ExpansionParameterModels
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels

def_wanted nativeCanonicalRamificationFamily (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) : CanonicalRamificationFamily F K D

end WantedExt.AlgebraicGeometry.CameralRamificationCocyclesWanted
