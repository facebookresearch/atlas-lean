/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalGroupoidPathDiagonalFibre
import MathlibExt.AlgebraicTopology.SimplicialSpace.LeftDecalageObjectLoopEquivalence
import MathlibExt.AlgebraicTopology.SimplicialSet.SharpRealizationFibre

/-!
# The original Segal groupoid mapping space and based diagonal loops

The complete original mapping fibre at an object maps to the compact-open
loops of the original diagonal at that same object. Its map is the original
zero-row/Rezk fibre comparison, the original constant-path homotopy-fibre
comparison, and the actual full-path return from whole path conullity.
Segal locality and equivalence of every original edge prove it weak.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u

open CategoryTheory CategoryTheory.Limits Opposite Topology
open scoped Simplicial

namespace SimplicialSpace.LeftDecalageObject

open SimplicialSpace.SegalHomotopy

/-- The original diagonal point fibre uses precisely the original vertex's complete Yoneda map. -/
def diagonalPointFibreIso (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    pullback (diagonalProjection W x) (diagonalPoint W y) ≅
      pullback (diagonalProjection W x) (SSet.yonedaEquiv.symm
        (show (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ from y)) :=
  pullback.congrHom rfl (diagonalPoint_eq_yoneda W y)

/-- The original mapping fibre enters the full compact-open path homotopy fibre at its same original target. -/
def mappingToDiagonalHomotopyFibre (W : SimplicialSpace.{u})
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.toTop.obj (mappingFibre W x y) ⟶
      TopCat.homotopyFiber (realizedDiagonalProjection W x) (realizedDiagonalPoint W y) :=
  SSet.toTop.map (mappingToDiagonalFibre W x y) ≫
    SSet.toTop.map (diagonalPointFibreIso W x y).hom ≫
      SSet.SharpComparisonDraft.pointFibreHomotopyComparison (diagonalProjection W x)
        (SSet.yonedaEquiv.symm
          (show (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ from y))

/-- Genuine original Segal groupoid hypotheses prove the actual mapping-to-homotopy-fibre map weak. -/
theorem mappingToDiagonalHomotopyFibre_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, IsEquivalenceEdge W hW a)
    (x y : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.weakHomotopyEquivalences (mappingToDiagonalHomotopyFibre W x y) := by
  have hm : TopCat.weakHomotopyEquivalences (SSet.toTop.map (mappingToDiagonalFibre W x y)) :=
    mappingToDiagonalFibre_weak W hW hG x y
  have hi : TopCat.weakHomotopyEquivalences (SSet.toTop.map (diagonalPointFibreIso W x y).hom) :=
    TopCat.weakHomotopyEquivalences.of_isIso _
  have hp := SSet.SharpComparisonDraft.pointFibreHomotopyComparison_weak (diagonalProjection W x)
    (diagonal_sharp_and_row_comparisons W hW hG x).1
    (SSet.yonedaEquiv.symm
      (show (SSet.simplicialDiagonalFunctor.obj W.diagram) _⦋0⦌ from y))
  exact TopCat.weakHomotopyEquivalences.comp_mem _ _ hm
    (TopCat.weakHomotopyEquivalences.comp_mem _ _ hi hp)

/-- The actual whole original endomorphism mapping fibre maps to the based diagonal loop space. -/
def mappingLoopComparison (W : SimplicialSpace.{u}) (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    SSet.toTop.obj (mappingFibre W x x) ⟶
      TopCat.of (LoopSpace (SSet.toTop.obj (SSet.simplicialDiagonalFunctor.obj W.diagram))
        (realizedDiagonalPoint W x)) :=
  mappingToDiagonalHomotopyFibre W x x ≫ diagonalHomotopyFibreToLoops W x

/-- The same actual mapping-to-loop comparison is weak for every original object of a Segal groupoid. -/
theorem mappingLoopComparison_weak (W : SimplicialSpace.{u}) (hW : segalSpaces W)
    (hG : ∀ a : (W.diagram _⦋1⦌) _⦋0⦌, IsEquivalenceEdge W hW a)
    (x : (W.diagram _⦋0⦌) _⦋0⦌) :
    TopCat.weakHomotopyEquivalences (mappingLoopComparison W x) :=
  TopCat.weakHomotopyEquivalences.comp_mem _ _
    (mappingToDiagonalHomotopyFibre_weak W hW hG x x)
    (diagonalHomotopyFibreToLoops_weak W x)

end SimplicialSpace.LeftDecalageObject
