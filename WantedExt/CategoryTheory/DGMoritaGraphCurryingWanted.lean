/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

public import Batteries.Util.ProofWanted
public import MathlibExt.CategoryTheory.DGMoritaGraphCurryingModels

/-!
# Source-normalized tensor-graph currying and derived closedness

Toën, arXiv:math/0408337v7, Theorem6.1, printed pp31–34.
The constructor chooses the native adjunction and graph-normalized
object comparisons jointly. The enriched bar replacement acts on the
actual column-cofibrant bimodule category; its maps retain the full
E-action. Construction proofs remain explicit requests.
-/

set_option autoImplicit false
@[expose] public noncomputable section
namespace WantedExt.CategoryTheory.DGMoritaGraphCurryingWanted

open _root_.CategoryTheory
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGMoritaClosedModels
open MathlibExt.CategoryTheory.DGMoritaGraphCurryingModels

universe u

def_wanted tensor_graph_currying (k : Type u) [CommRing k]
    (E C D : DGCat k) (F : tensor E C ⟶ D) : GraphCurrying F

def_wanted column_cofibrant_bimodule_replacement (k : Type u) [CommRing k]
    (C D : DGCat k) (cofibrant : IsCofibrant C) : BimoduleReplacementFunctor C D

def_wanted source_normalized_morita_closedness (k : Type u) [CommRing k]
    (Q : ReplacementFunctor k) (C : DGCat k) (T : LocalizedTensorModel Q C) :
    Σ M : MoritaClosedModel Q C T, NormalizedClosedModel M

end WantedExt.CategoryTheory.DGMoritaGraphCurryingWanted
