/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Topology.Category.TopCat.RealizedPointCofibration
import MathlibExt.Topology.CWComplex.BasedWhitehead

noncomputable section

open CategoryTheory HomotopicalAlgebra
open scoped Simplicial TopCat.modelCategory

universe u

#check @SSet.realizedVertex_pointMap_cofibration
#print axioms SSet.realizedVertex_pointMap_cofibration

example (K : SSet.{u}) (v : K _⦋0⦌) :
    Cofibration (TopCat.const (SSet.realizedVertex v) :
      TopCat.of PUnit.{u + 1} ⟶ SSet.toTop.obj K) :=
  SSet.realizedVertex_pointMap_cofibration K v

-- Both point hypotheses of the generic based theorem are ACTUALLY derived.
example (K L : SSet.{u}) (x : K _⦋0⦌) (y : L _⦋0⦌)
    (f : SSet.toTop.obj K ⟶ SSet.toTop.obj L)
    (hxy : f (SSet.realizedVertex x) = SSet.realizedVertex y)
    (hf : TopCat.weakHomotopyEquivalences f) :
    ∃ g : SSet.toTop.obj L ⟶ SSet.toTop.obj K,
      g (SSet.realizedVertex y) = SSet.realizedVertex x ∧
        Nonempty (ContinuousMap.HomotopyRel (f ≫ g).hom (TopCat.Hom.hom (𝟙 (SSet.toTop.obj K))) {SSet.realizedVertex x}) ∧
        Nonempty (ContinuousMap.HomotopyRel (g ≫ f).hom (TopCat.Hom.hom (𝟙 (SSet.toTop.obj L))) {SSet.realizedVertex y}) := by
  let := SSet.realizedVertex_pointMap_cofibration K x
  let := SSet.realizedVertex_pointMap_cofibration L y
  exact TopCat.exists_based_inverse_of_weak_of_cofibrant_points
    _ _ (SSet.realizedVertex x) (SSet.realizedVertex y) f hxy hf

end
