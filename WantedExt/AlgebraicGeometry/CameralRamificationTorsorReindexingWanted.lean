/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralRamificationTorsorReindexing

/-!
# Native full ramification-frame and coroot-pushout reindexing

The field compares actual frame bases on every coefficient scheme and
actual coroot quotient points. Finite tensor pullbacks are already the
native recursive tensor comparison in MathlibExt.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 5.2--5.5.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralRamificationTorsorReindexingWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationReindexing
open CameralRamificationTensorModels CameralRamificationTorsorReindexing ExpansionParameterModels
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels

def_wanted nativeRamificationTorsorReindexing (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) (R : RamificationReindexing F) : TorsorReindexing F K D R

end WantedExt.AlgebraicGeometry.CameralRamificationTorsorReindexingWanted
