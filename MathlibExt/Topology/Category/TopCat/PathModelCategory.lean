/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Topology.Category.TopCat.HomotopyFiberBaseChange
public import MathlibExt.AlgebraicTopology.SimplicialSet.ModelCategory.Realization.ContinuousWhitehead

/-!
# Initial evaluation of the compact-open path object

The selected TopCat model structure makes initial path evaluation a trivial
fibration for every topological target. The proof uses the existing endpoint
fibration, fibrancy of every target, and weak initial evaluation.
-/

public section

noncomputable section

open CategoryTheory CategoryTheory.Limits HomotopicalAlgebra
open scoped TopCat.modelCategory

universe u

namespace TopCat.PathModelCategory

private theorem pathEvalZero_fibration (Y : TopCat.{u}) :
    Fibration (TopCat.pathEvalZero Y) := by
  let _ : Fibration (TopCat.pathEndpoints Y) :=
    TopCat.modelCategory.pathEndpoints_fibration Y
  let _ : IsFibrant Y := SSet.RealizationCWUpgrade.allTopCatObjectsFibrant Y
  have h : TopCat.pathEvalZero Y =
      TopCat.pathEndpoints Y ≫ (prod.fst : Y ⨯ Y ⟶ Y) := by
    simp [TopCat.pathEndpoints]
  rw [h]
  infer_instance

/-- Initial evaluation of the ACTUAL compact-open path object is
a trivial fibration in the selected TopCat model structure. The existing
arbitrary-target endpoint-fibration proof and weak evaluation are reused. -/
public theorem _root_.TopCat.pathEvalZero_trivialFibration (Y : TopCat.{u}) :
    trivialFibrations TopCat.{u} (TopCat.pathEvalZero Y) := by
  let : Fibration (TopCat.pathEvalZero Y) := pathEvalZero_fibration Y
  let : WeakEquivalence (TopCat.pathEvalZero Y) :=
    (weakEquivalence_iff _).mpr (TopCat.pathEvalZero_mem_weakHomotopyEquivalences Y)
  exact mem_trivialFibrations (TopCat.pathEvalZero Y)

end TopCat.PathModelCategory

end
