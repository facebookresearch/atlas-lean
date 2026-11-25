/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralLiftedNormalizerModels

/-!
# Actual root transport and simple-reflection comparisons

The transported parameter is the actual SL2 parameter multiplied by the
inverse native adjoint coefficient. The square is the coroot at minus
one, with no assumption that this element survives in G. The simple
reflection torsor comparison uses canonical universal frames and every
Cartesian coefficient pullback.
Source: DG arXiv:math/0005132v3, Sections 6.1--6.2 and 8.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralLiftedNormalizerModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRootSL2Sources CameralRamificationTensorModels
open CameralRamificationCocycles CameralNormalizerShifts CameralLiftedNormalizerModels
open ExpansionParameterModels GeneralLinearFrameSchemes RankTwoMatrixGroupModels

def_wanted nativeRootWeylGeometry (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F) :
    RootWeylGeometry F K

def_wanted nativeSimpleReflectionTorsors (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (D : RootTorsorInputs F K) (R : CanonicalRamificationFamily F K D) :
    SimpleReflectionTorsors F K D R

def_wanted nativeTransportedNormalizerLift (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (U : Over (Spec (.of ℂ))) (n : U ⟶ F.normalizer.scheme) (w : F.Weyl) (hn : Label F n w)
    (i j : Fin F.roots.count) (hij : K.permutations.index w i = j) (c : U ⟶ torusScheme ℂ 1) :
    TransportedNormalizerLift F K U n w hn i j hij c

theorem_wanted rootNormalizerSquare (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    [FrameTheory 2] [GL2MatrixTheory] [SL2MatrixTheory] (K : RootNormalizerGeometry G tori F)
    (i : Fin F.roots.count) (U : Over (Spec (.of ℂ))) (c : U ⟶ torusScheme ℂ 1) :
    normalizerProduct F (c ≫ (K.sl2 i).normalizer) (c ≫ (K.sl2 i).normalizer) ≫
      F.normalizer.inclusion = minusOne (tori := tori) U ≫ F.roots.coroot i ≫ F.source.torus

end WantedExt.AlgebraicGeometry.CameralLiftedNormalizerModelsWanted
