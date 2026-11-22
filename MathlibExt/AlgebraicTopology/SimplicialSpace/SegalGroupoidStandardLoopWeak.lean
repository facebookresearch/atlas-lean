/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidNativeLoopFormula
import MathlibExt.Topology.Category.TopCat.LoopConstantTail
import MathlibExt.Topology.Category.TopCat.WeakHomotopyEquivalenceHomotopy

/-!
# The standard mapping-space loop comparison for a Segal groupoid

For an original Reedy fibrant Segal space whose original edges are all
equivalences, its standard original diagonal edge-loop map is a weak
homotopy equivalence. The proof compares the actual native contraction
return with this same map through the continuous constant-tail homotopy.
Completeness is unnecessary for this statement.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

open SimplicialSpace.SegalHomotopy

/-- The actual native return factors through the same standard original loop map and its constant tail. -/
theorem nativeMappingLoopComparison_eq_standard_tail (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    nativeMappingLoopComparison W x =
      standardDiagonalLoopMap W x ≫ TopCat.loopConstantTailMap
        (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram)) (realizedDiagonalPoint W x) := by
  apply TopCat.ext
  intro z
  change nativeMappingLoopComparison W x z =
    TopCat.loopConstantTailMap (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram))
      (realizedDiagonalPoint W x) (standardDiagonalLoopMap W x z)
  rw [TopCat.loopConstantTailMap_apply]
  exact nativeMappingLoopComparison_formula W x z

/-- The genuine original Segal groupoid data makes the standard original edge-loop map weak. -/
theorem standardDiagonalLoopMap_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, IsEquivalenceEdge W hW a)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.weakHomotopyEquivalences (standardDiagonalLoopMap W x) := by
  let B := SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram)
  let b := realizedDiagonalPoint W x
  let f := standardDiagonalLoopMap W x
  let H := (TopCat.loopConstantTailHomotopy B b).compContinuousMap f.hom
  have h0 : (TopCat.loopConstantTailMap B b).hom.comp f.hom =
      (nativeMappingLoopComparison W x).hom := by
    have he := congrArg TopCat.Hom.hom (nativeMappingLoopComparison_eq_standard_tail W x)
    exact (TopCat.hom_comp f (TopCat.loopConstantTailMap B b)).symm.trans he.symm
  have h1 : (ContinuousMap.id (LoopSpace B b)).comp f.hom = f.hom := rfl
  exact (TopCat.weakHomotopyEquivalences_iff_of_homotopy (H.cast h0 h1)).mp
    (nativeMappingLoopComparison_weak W hW hG x)

end SimplicialSpace.LeftDecalageObject
