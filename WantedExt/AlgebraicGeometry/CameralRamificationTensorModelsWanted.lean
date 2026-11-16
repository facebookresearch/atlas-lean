/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralRamificationTensorModels

/-!
# Native root torsor pushouts and combined Weyl comparisons

R_w is already the actual coroot/tensor construction. The targets construct
the finite root and Weyl pushout operations and normalized comparisons
for the actual scheme pullbacks and inverse torus actions.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 5.2--5.8.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralRamificationTensorModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels ExpansionParameterModels
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels

def_wanted nativeCameralRootTorsorInputs (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F) :
    RootTorsorInputs F K

def_wanted nativeCombinedWeylCalculus (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) {X : Over (Spec (.of ℂ))} (C : Cover F X) : WeylCalculus F K D C

end WantedExt.AlgebraicGeometry.CameralRamificationTensorModelsWanted
