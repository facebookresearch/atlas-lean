/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidPathFibreReadback

/-!
# The original mapping-to-homotopy-fibre comparison carries the constant target path

The actual original diagonal point fibre enters the compact-open homotopy
fibre by the constant path at its same prescribed target. Every original
mapping-space point retains that whole constant path.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

/-- The complete original mapping-to-homotopy-fibre comparison carries the literal constant target path. -/
theorem mappingToDiagonalHomotopyFibre_path (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    mappingToDiagonalHomotopyFibre W x y ≫
        TopCat.homotopyFiberPath (realizedDiagonalProjection W x) (realizedDiagonalPoint W y) =
      (TopCat.const (ContinuousMap.const TopCat.I.{u} (realizedDiagonalPoint W y)) :
        SSet.toTop.obj (mappingFibre W x y) ⟶
          TopCat.pathObject (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram))) := by
  let yD : (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ := y
  let b := SSet.yonedaEquiv.symm yD
  have hp := SSet.SharpComparisonDraft.pointFibreHomotopyComparison_path (diagonalProjection W x) b
  apply TopCat.ext
  intro z
  apply ContinuousMap.ext
  intro t
  change TopCat.homotopyFiberPath (SSet.toTop.map (diagonalProjection W x)) (SSet.realizedPoint b)
    ((SSet.toTop.map (mappingToDiagonalFibre W x y) ≫ SSet.toTop.map (diagonalPointFibreIso W x y).hom ≫
      SSet.SharpComparisonDraft.pointFibreHomotopyComparison (diagonalProjection W x) b) z) t = _
  have he := ConcreteCategory.congr_hom hp
    (SSet.toTop.map (diagonalPointFibreIso W x y).hom (SSet.toTop.map (mappingToDiagonalFibre W x y) z))
  have ht := congrArg (fun p : TopCat.pathObject
      (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram)) => p t) he
  exact ht

end SimplicialSpace.LeftDecalageObject
