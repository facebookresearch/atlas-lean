/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralCharacterRealizations

/-!
# Native character-line construction

The frame scheme is the actual character pushout. All module arrows and
Cartesian pullbacks are normalized on every scheme-valued frame.
Source: DG arXiv:math/0005132v3, Sections 5--6; Stacks Project Tag 0CQJ.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralCharacterRealizationsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationTensorModels
open CameralCharacterRealizations ExpansionParameterModels GeneralLinearFrameSchemes
open RankTwoMatrixGroupModels

def_wanted nativeCharacterCalculus (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) : CharacterCalculus F K D

end WantedExt.AlgebraicGeometry.CameralCharacterRealizationsWanted
