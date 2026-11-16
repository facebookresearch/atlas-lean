/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralNormalizerShifts

/-!
# Native parameter covers and assembly of normalizer shifts

These requests construct Cartesian parameter covers, actual torus
translations, and assembly from given compatible constant-label shifts
on the native clopen cover. Arbitrary T bundles are not asserted to
admit an N shift. The assembled object is fixed by the actual local maps.
Source: DG arXiv:math/0005132v3, Sections 6.2--6.3.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralNormalizerShiftsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationTensorModels
open CameralRamificationReindexing CameralRamificationCocycles CameralNormalizerShifts
open ContractedTorsorModels ExpansionParameterModels GeneralLinearFrameSchemes
open RankTwoMatrixGroupModels

attribute [local instance] CameralRamificationTensorModels.torusGroup

def_wanted nativeParameterCovers (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) : ParameterCovers F C

def_wanted nativeTorusTranslation (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (B : ParameterCovers F C) (L : Bundle (Torus F) (total F C))
    (U : Over (Spec (.of ℂ))) (t : U ⟶ Torus F) : TorusTranslation F K D B L U t

def_wanted nativeNormalizerAssembly (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) (R : CanonicalRamificationFamily F K D)
    (X : Over (Spec (.of ℂ))) (C : Cover F X) (B : ParameterCovers F C)
    (L : Bundle (Torus F) (total F C)) (S : ConstantNormalizerShift F K D R B L) :
    FullNormalizerShift F K D R B L S

end WantedExt.AlgebraicGeometry.CameralNormalizerShiftsWanted
