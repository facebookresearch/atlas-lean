/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralRootSL2Sources

/-!
# Native rank-one root and lifted normalizer construction

The group is actually reductive through rational representations. The
existing foundation fixes its actual Lie, torus, full Cartan reflections,
normalizer and Chevalley scheme. The target adds actual root SL2 maps and
the coefficient-normalized lifted conjugations needed for ramification beta.
Existing frame and GL2/SL2 scheme dictionaries are reused.
Source: Donagi--Gaitsgory arXiv:math/0005132v3, Sections 5--6 and 8.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralRootSL2SourcesWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry
open _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources ReductiveGroupHypotheses
open ExpansionParameterModels GeneralLinearFrameSchemes RankTwoMatrixGroupModels

def_wanted nativeRootNormalizerGeometry (G : Over (Spec (.of ℂ))) [GrpObj G]
    [IsAffine G.left] [ConnectedSpace G.left] [Smooth G.hom] [LocallyOfFiniteType G.hom]
    (hRed : IsLinearlyReductive G) (tori : ∀ n : ℕ, TorusTheory ℂ n)
    (F : Foundation G tori) [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] :
    RootNormalizerGeometry G tori F

end WantedExt.AlgebraicGeometry.CameralRootSL2SourcesWanted
