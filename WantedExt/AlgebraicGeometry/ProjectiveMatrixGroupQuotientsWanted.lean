/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.ProjectiveMatrixGroupQuotients

/-!
# Native projective matrix quotient and effective character action requests

The result is the actual scalar fppf quotient of GL2 and the actual
projective-group torsor above its fixed invariant-function quotient.
The source genus range remains explicit; no matrix-orbit classification
over a single field is assumed.
Source: de Cataldo--Hausel--Migliorini arXiv:1004.1420v2,
Introduction and Section1.2.1; Stacks Project Tag0CQJ.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.ProjectiveMatrixGroupQuotientsWanted

open _root_.MathlibExt.AlgebraicGeometry
open GeneralLinearFrameSchemes RankTwoMatrixGroupModels ExpansionParameterModels
open TwistedRankTwoRepresentations TwistedCharacterQuotientModels ProjectiveMatrixGroupQuotients

def_wanted nativeProjectiveGL2
    [F : FrameTheory 2] [M : GL2MatrixTheory] (Gm : TorusTheory ℂ 1) : ProjectiveGL2 Gm

def_wanted nativeEffectiveCharacterTorsor
    [F : FrameTheory 2] [M : GL2MatrixTheory] {Gm : TorusTheory ℂ 1}
    (P : ProjectiveGL2 Gm) (g : ℕ) (stableRange : 2 ≤ g)
    [C : Conjugation g] [Q : CharacterQuotient g] : CharacterTorsor P g

end WantedExt.AlgebraicGeometry.ProjectiveMatrixGroupQuotientsWanted
