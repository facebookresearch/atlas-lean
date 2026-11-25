/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGMoritaClosedModels

/-!
# Wanted derived DG closedness on the fixed native tensor

Construct the native right adjoint and its actual cofibrant
right-quasi-representable DG model. The adjunction and the source-model
quasi-equivalence are outputs, not assumptions in the input tensor or
replacement contracts.

Reference: Toën, arXiv:math/0408337v7, Theorem 6.1, printed p.31.
Tasks whose target constructs the tensor or replacement must prove that
construction as part of their task rather than pass it as background.
-/

namespace WantedExt.AlgebraicGeometry.DGMoritaClosedModelsWanted

open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGMoritaClosedModels

universe u

/-- **The derived tensor product of DG categories has a right adjoint.** Toën, Theorem 6.1: for
a commutative ring $k$, a cofibrant replacement functor $Q$ for DG categories over $k$, a DG
category $C$ and a model $T$ of the derived tensor product with $C$ on the homotopy category of DG
categories (sending $A$ to $QA \otimes QC$): a right adjoint of $T$, together with, for every DG
category $D$, a small DG category quasi-equivalent to the DG category of cofibrant, right
quasi-representable bimodules from $QC$ to $D$, and an isomorphism, in the homotopy category,
between the value of the right adjoint at $D$ and this small DG category
(`MoritaClosedModel Q C T`). -/
def_wanted dg_morita_closed_model (k : Type u) [CommRing k]
    (Q : ReplacementFunctor k) (C : DGCat k) (T : LocalizedTensorModel Q C) :
  MoritaClosedModel Q C T

end WantedExt.AlgebraicGeometry.DGMoritaClosedModelsWanted
