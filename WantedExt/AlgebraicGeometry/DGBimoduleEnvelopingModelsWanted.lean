/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels

/-!
# Wanted actual bimodule/enveloping normalization

The right module over Cᵒᵖ⊗D is fixed on every point and pure
homogeneous tensor action. The diagonal remains the native identity graph.
References: Toën math/0408337v7 §3; Keller, Deriving DG categories §6.
-/

namespace WantedExt.AlgebraicGeometry.DGBimoduleEnvelopingModelsWanted

open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGBimoduleEnvelopingModels

universe u

/-- Uncurry the actual curried DG bimodule with the specified tensor actions. -/
def_wanted dg_bimodule_enveloping_module (k : Type u) [CommRing k]
    (C D : DGCat k) (M : Bimodule k C D) : EnvelopingModuleModel M

end WantedExt.AlgebraicGeometry.DGBimoduleEnvelopingModelsWanted
