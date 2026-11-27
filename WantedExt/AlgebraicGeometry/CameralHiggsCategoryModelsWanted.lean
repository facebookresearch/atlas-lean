/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.AlgebraicGeometry.CameralHiggsCategoryModels

/-!
# Native Higgs arrow and module pullback coherence

The requested proofs concern the displayed identity/composition maps.
The pullback object has the literal original torsor, pulled modules,
inclusion and whole K-valued section. No equivalence theorem is an input.
Source: DG math/0005132v3, Sections17.1--17.7.
-/

set_option autoImplicit false
@[expose] public noncomputable section

namespace WantedExt.AlgebraicGeometry.CameralHiggsCategoryModelsWanted

open _root_.CategoryTheory _root_.AlgebraicGeometry _root_.MathlibExt.AlgebraicGeometry
open CameralFoundationPackages CameralRegularizedHiggsModels CameralHiggsCategoryModels
open ExpansionParameterModels GroupTorsorGeometry RelativeLambdaReindexing
open CoherentCurveLinearSeries

attribute [local instance] centralizerGroupAction

theorem_wanted nativeHiggsCategoryCoherence (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X : Over (Spec (.of ℂ))) (K : TwistLine X) : CategoryCoherence F (X := X) (K := K)

def_wanted nativeHiggsPullback (G : Over (Spec (.of ℂ))) [GrpObj G]
    (tori : ∀ n : ℕ, TorusTheory ℂ n) (F : Foundation G tori)
    (X Y : Over (Spec (.of ℂ))) (K : TwistLine X) (f : Y ⟶ X)
    (hK : IsLineBundle ((Scheme.Modules.pullback f.left).obj K.module))
    (H : RegularizedBundle F X K) (r : Reindex G H.regularizer.torsor f)
    (T : TensorPullbackComparison f.left) : PullbackBundle F f hK H r T

end WantedExt.AlgebraicGeometry.CameralHiggsCategoryModelsWanted
