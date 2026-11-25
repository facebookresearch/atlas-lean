/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralRegularizedHiggsModels

/-!
# Native regularized centralizer descent

These are direct construction/proof requests for the displayed actual
schemes, modules, torsors and normalized maps. Their definitions and
completed source ports remain in MathlibExt.
Source: DG arXiv:math/0005132v3, Sections 2 and 17.1--17.4.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.AlgebraicGeometry.CameralRegularizedHiggsModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages ExpansionParameterModels
open CameralRegularizedHiggsModels
attribute [local instance] CameralRegularizedHiggsModels.centralizerGroupAction

def_wanted nativeAdjointBundle (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X : Over (Spec (.of ℂ))) (P : Regularizer F X) : AdjointBundle F P

def_wanted nativeCentralizerBundle (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X : Over (Spec (.of ℂ))) (P : Regularizer F X) (A : AdjointBundle F P) :
    CentralizerBundle F P A

end WantedExt.AlgebraicGeometry.CameralRegularizedHiggsModelsWanted
