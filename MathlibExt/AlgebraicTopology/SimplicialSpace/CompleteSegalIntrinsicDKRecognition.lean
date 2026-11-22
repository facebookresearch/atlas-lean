/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LocalWhitehead
import MathlibExt.AlgebraicTopology.SimplicialSpace.CompleteSegalLevelwiseWeakComparison
import MathlibExt.AlgebraicTopology.SimplicialSpace.IntrinsicDKComposition

/-!
# Dwyer–Kan recognition between complete Segal spaces

For a map between complete Segal spaces, the Rezk weak-equivalence predicate is equivalent to
intrinsic Dwyer–Kan equivalence. Completeness supplies the required Reedy-fibrant Segal
structures, and the comparison identifies the original levelwise weak condition with mapping-
fibre weakness and homotopy-category essential surjectivity.
-/

set_option autoImplicit false
noncomputable section
universe u
open CategoryTheory HomotopicalAlgebra Opposite
open scoped Simplicial SimplicialSpace.Inner
attribute [local instance] SimplicialSpace.ReedyModel.modelCategory
namespace SimplicialSpace

/-- At complete endpoints the specified original CSS weak class is exactly intrinsic DK. -/
theorem completeSegalMap_cssWeak_iff_intrinsicDK {W V : SimplicialSpace.{u}} (f : W ⟶ V)
    (hW : completeSegalSpaces W) (hV : completeSegalSpaces V) :
    rezkWeakEquivalences f ↔
      IntrinsicDK.isEquivalence f
        (((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete W).mp hW).1)
        (((FiniteCompletenessHorel.completeSegalSpaces_iff_finiteComplete V).mp hV).1) := by
  have hc := completeSegalMap_levelwiseWeak_iff f hW hV
  have hl : rezkWeakEquivalences f ↔
      ∀ n : ℕ, SSet.realizationWeakEquivalences (f.hom.app (op ⦋n⦌)) :=
    (rezkWeak_iff_reedyWeak_of_completeSegalSpaces f hW hV).trans
      (ReedyModel.weakEquivalence_iff f)
  simpa only [IntrinsicDK.isEquivalence] using hl.trans hc.symm

end SimplicialSpace
