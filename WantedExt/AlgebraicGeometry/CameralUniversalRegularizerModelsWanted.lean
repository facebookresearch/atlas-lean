/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralUniversalRegularizerModels

/-!
# Universal regularizer and original torsor-action comparison

The source is the actual trivial G torsor over RegCent, with sigma
equal to the original adjoint action and the whole marked incidence
cover. The all-family comparison is the native torsor action relation.
Source: DG math/0005132v3, Sections2/7/16.1.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralUniversalRegularizerModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralCoverDescentModels CameralRamificationReindexing
open CameralUniversalRegularizerModels CameralUnramifiedNormalizerModels
open CameralBorelAbelianizationCore ExpansionParameterModels

attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

def_wanted nativeUniversalRegularizer (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G) (I : IncidenceAction F) :
    UniversalRegularizer F I

def_wanted nativeOriginalActionComparison (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (U : UniversalRegularizer F I) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (H : Marked F I C) : OriginalActionComparison F I U H

def_wanted nativeOriginalCoverComparison (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori) (I : IncidenceAction F)
    (U : UniversalRegularizer F I) (X : Over (Spec (.of ℂ))) (C : Cover F X)
    (H : Marked F I C) (P : OriginalActionComparison F I U H) :
    OriginalCoverComparison F I U H P

theorem_wanted nativeUniversalCartanOpen (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G) (Z : CartanPoint F) :
    CartanOpen F Z

theorem_wanted nativeUniversalCartanDense (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (_hred : ReductiveGroupHypotheses.IsLinearlyReductive G) (Z : CartanPoint F) :
    DenseRange (cartanOrbit F Z).left

end WantedExt.AlgebraicGeometry.CameralUniversalRegularizerModelsWanted
