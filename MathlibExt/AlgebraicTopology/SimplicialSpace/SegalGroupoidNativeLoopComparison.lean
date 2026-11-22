/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectNativeBasedContraction
import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidPathFibreReadback

/-!
# The original Segal groupoid loop comparison from its actual native contraction

Use the actual original extra-degeneracy based contraction in the full
path-fibre/loop equivalence. The original mapping-fibre comparison remains
weak and retains its entire original zero-row total map and carried path.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

open SimplicialSpace.SegalHomotopy

/-- The actual full path-fibre loop equivalence now uses the original native extra-degeneracy contraction. -/
def nativeDiagonalHomotopyFibreLoopEquiv (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    ContinuousMap.HomotopyEquiv
      (TopCat.homotopyFiber (realizedDiagonalProjection W x) (realizedDiagonalPoint W x))
      (LoopSpace (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram)) (realizedDiagonalPoint W x)) :=
  TopCat.homotopyFiberLoopEquivOfBasedContraction (realizedDiagonalProjection W x)
    (SSet.realizedVertex (diagonalBasepoint W x)) (realizedDiagonalPoint W x)
    (realizedBasepoint_projection W x) (nativeBasedContraction W x)

/-- The whole original mapping fibre maps into based loops using the same native contraction. -/
def nativeMappingLoopComparison (W : SimplicialSpace.{u})
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.toTop.obj (mappingFibre W x x) ⟶
      TopCat.of (LoopSpace (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram))
        (realizedDiagonalPoint W x)) :=
  mappingToDiagonalHomotopyFibre W x x ≫ TopCat.ofHom (nativeDiagonalHomotopyFibreLoopEquiv W x).toFun

/-- Genuine original Segal groupoid hypotheses make the same native contraction comparison weak. -/
theorem nativeMappingLoopComparison_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, IsEquivalenceEdge W hW a)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.weakHomotopyEquivalences (nativeMappingLoopComparison W x) :=
  TopCat.weakHomotopyEquivalences.comp_mem _ _
    (mappingToDiagonalHomotopyFibre_weak W hW hG x x)
    (TopCat.homotopyEquiv_toFun_mem (nativeDiagonalHomotopyFibreLoopEquiv W x))

end SimplicialSpace.LeftDecalageObject
