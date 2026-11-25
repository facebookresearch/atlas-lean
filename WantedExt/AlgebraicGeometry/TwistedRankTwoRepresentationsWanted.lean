/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.TwistedRankTwoRepresentations

/-!
# Native twisted representation point and action requests

Both targets are bound to the actual finite product, word fibre and
matrix projections. The GL2 provider is the existing frame dictionary.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Section1.2.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.TwistedRankTwoRepresentationsWanted

open _root_.MathlibExt.AlgebraicGeometry
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels TwistedRankTwoRepresentations

def_wanted nativeTwistedRepresentationPoints
    [F : FrameTheory 2] [M : GL2MatrixTheory] (g : ℕ) : PointModel g

def_wanted nativeTwistedRepresentationConjugation
    [F : FrameTheory 2] [M : GL2MatrixTheory] (g : ℕ) : Conjugation g

end WantedExt.AlgebraicGeometry.TwistedRankTwoRepresentationsWanted
