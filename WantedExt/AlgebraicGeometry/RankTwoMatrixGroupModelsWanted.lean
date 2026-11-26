/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.RankTwoMatrixGroupModels

/-!
# Native matrix dictionaries for the existing frame scheme

The actual GL2 frame provider is an explicit reused input. The first
request integrates its finite-free module automorphisms with their native
global-function matrices; the second constructs the determinant-one
fibre and its native matrix/group inclusion.
Sources: Donagi--Gaitsgory arXiv:math/0005132v3, Sections6--8;
de Cataldo--Hausel--Migliorini arXiv:1004.1420v2, Section1.2.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.RankTwoMatrixGroupModelsWanted

open _root_.MathlibExt.AlgebraicGeometry
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels

def_wanted nativeGL2MatrixDictionary [F : FrameTheory 2] : GL2MatrixTheory

def_wanted nativeSL2MatrixDictionary [F : FrameTheory 2] [M : GL2MatrixTheory] : SL2MatrixTheory

end WantedExt.AlgebraicGeometry.RankTwoMatrixGroupModelsWanted
