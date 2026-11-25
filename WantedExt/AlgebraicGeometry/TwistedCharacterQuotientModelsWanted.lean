/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.TwistedCharacterQuotientModels

/-!
# Native twisted character quotient construction request

The quotient scheme and morphism are already defined from the actual
regular-function invariants. The target supplies their actual GIT
universal property and smooth complex-variety conditions in the source
stable genus range.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Section1.2.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.TwistedCharacterQuotientModelsWanted

open _root_.MathlibExt.AlgebraicGeometry
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels TwistedRankTwoRepresentations
open TwistedCharacterQuotientModels

def_wanted nativeTwistedCharacterQuotient
    [F : FrameTheory 2] [M : GL2MatrixTheory] (g : ℕ) (stableRange : 2 ≤ g)
    [C : Conjugation g] : CharacterQuotient g

end WantedExt.AlgebraicGeometry.TwistedCharacterQuotientModelsWanted
