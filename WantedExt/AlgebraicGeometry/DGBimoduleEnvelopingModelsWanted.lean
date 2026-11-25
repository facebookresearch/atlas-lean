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

/-- **The enveloping module of a DG bimodule.** For a commutative ring $k$, DG categories $C$ and
$D$ over $k$ and a DG bimodule $M$, given as a DG functor from $C$ to right DG $D$-modules: a right
DG module over the enveloping DG category $C^{\mathrm{op}} \otimes D$ whose value at $(x, y)$ is
$M(x)(y)$, and whose action of each homogeneous pure tensor $a \otimes b$, with $a : x \to x'$ in
$C$ of degree $p$ and $b : y \to y'$ in $D^{\mathrm{op}}$ of degree $q$, is the action of $a$ at $y$
followed by the action of $b$ on $M(x')$ (`EnvelopingModuleModel M`). -/
def_wanted dg_bimodule_enveloping_module (k : Type u) [CommRing k]
    (C D : DGCat k) (M : Bimodule k C D) : EnvelopingModuleModel M

end WantedExt.AlgebraicGeometry.DGBimoduleEnvelopingModelsWanted
