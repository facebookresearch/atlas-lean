/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralHitchinFamilyModels

/-!
# Native regularized Higgs coefficient families and algebraic Hitchin base

The family presentation is normalized on X times U, the literal K
pullback, every original torsor/module/section map, the whole Cartan
tautological section and the native stack unit/composition cells.
The algebraic base constructor retains the source proper-X hypothesis.
Source: DG math/0005132v3, Sections17.1--17.8.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralHitchinFamilyModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralCoverDescentModels CameralRegularizedHiggsModels
open CameralHiggsCategoryModels CameralCartanValueModels CameralHitchinFunctorModels
open CameralHitchinFamilyModels ExpansionParameterModels

attribute [local instance] centralizerGroupAction

def_wanted nativeHitchinParameters (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X : Over (Spec (.of ℂ))) (K : TwistLine X) : Parameters F K

def_wanted nativeHitchinStacks (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G)
    (I : IncidenceAction F) (X : Over (Spec (.of ℂ))) (K : TwistLine X)
    (_hproper : IsProper X.hom) (P : Parameters F K) : HitchinStacks F I K P

theorem_wanted nativeFibreArrowCoherence (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (X : Over (Spec (.of ℂ))) (K : TwistLine X)
    (S : SectionSpace X (cartanKModule F X K)) (W : CartanWeylAction F X K S)
    (b : ValueObject F K S W) : FibreArrowCoherence F I K S W b

end WantedExt.AlgebraicGeometry.CameralHitchinFamilyModelsWanted
