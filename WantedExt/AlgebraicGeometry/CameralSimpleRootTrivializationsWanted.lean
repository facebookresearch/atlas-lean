/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralSimpleRootTrivializations

/-!
# The Proposition 5.5 construction

The canonical twist-line trivialization is fixed on the actual universal
simple-root divisor by its section frames. Density is required there
only. All Cartesian cameral pullbacks use the full coefficient maps.
Source: DG arXiv:math/0005132v3, Proposition 5.5.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralSimpleRootTrivializationsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationTensorModels
open CameralRamificationCocycles CameralCharacterRealizations CameralSimpleRootTrivializations
open ExpansionParameterModels GeneralLinearFrameSchemes RankTwoMatrixGroupModels

def_wanted nativeSimpleRootTrivializations (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) (R : CanonicalRamificationFamily F K D)
    (A : CharacterCalculus F K D) : CanonicalSimpleRootTrivializations F K D R A

end WantedExt.AlgebraicGeometry.CameralSimpleRootTrivializationsWanted
