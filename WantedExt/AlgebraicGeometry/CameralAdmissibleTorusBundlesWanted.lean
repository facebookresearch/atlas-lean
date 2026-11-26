/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralAdmissibleTorusBundles

/-!
# Inverses of actual admissible torus-bundle arrows

The category already has the literal equivariant torsor arrows,
identity and composition, preserving all parameter gamma/beta data.
The remaining assertion proves preservation under the native inverse.
Source: DG arXiv:math/0005132v3, Section 6.2.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralAdmissibleTorusBundlesWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationTensorModels
open CameralRamificationReindexing CameralRamificationCocycles CameralCharacterRealizations
open CameralSimpleRootTrivializations CameralNormalizerShifts CameralLiftedNormalizerModels
open CameralAdmissibleTorusBundles ExpansionParameterModels GeneralLinearFrameSchemes
open RankTwoMatrixGroupModels

theorem_wanted admissibleIsGroupoid (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) (R : CanonicalRamificationFamily F K D)
    (A : CharacterCalculus F K D) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (B : ParameterCovers F C) (Q : SimpleReflectionTorsors F K D R) (E : RootWeylGeometry F K)
    (T : CanonicalSimpleRootTrivializations F K D R A) : IsGroupoid (Object F K D R A B Q E T)

end WantedExt.AlgebraicGeometry.CameralAdmissibleTorusBundlesWanted
