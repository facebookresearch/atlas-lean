/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import MathlibExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerDgCoherentGridSquare

/-! Tests for the DG coherent grid square. -/

namespace MathlibExtTest.AlgebraicGeometry.DGRelativeCYDiagramLedgerDgCoherentGridSquare

open CategoryTheory
open MathlibExt.DGSource
open MathlibExt.CategoryTheory.DGModelContracts
open MathlibExt.CategoryTheory.DGQuasiFunctorModels
open MathlibExt.CategoryTheory.DGModuleConeShiftModels
open MathlibExt.CategoryTheory.DGModuleUniversalConeModels
open MathlibExt.CategoryTheory.DGRelativeCYDiagramLedger
open MathlibExt.CategoryTheory.DGCoherentIndexModels
open WantedExt.AlgebraicGeometry.DGRelativeCYDiagramLedgerWanted

universe u

variable {k : Type u} [Field k]

example (R : CoherentIndexModel k GridIndex) (C : DGCat k) (Q : CoherentDiagram R C)
    (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj) :
    CoherentSquareModel Q nodes eq .upperLeft :=
  dg_coherent_grid_square k R C Q nodes eq .upperLeft

example (R : CoherentIndexModel k GridIndex) (C : DGCat k) (Q : CoherentDiagram R C)
    (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj) :
    dgDifferential k (-1) (squareCell Q nodes eq .lowerRight) =
      moduleCycle (arrowAtNodes Q nodes eq _ _ (SmallSquare.top_lt .lowerRight) ≫
        arrowAtNodes Q nodes eq _ _ (SmallSquare.right_lt .lowerRight)) -
      moduleCycle (arrowAtNodes Q nodes eq _ _ (SmallSquare.left_lt .lowerRight) ≫
        arrowAtNodes Q nodes eq _ _ (SmallSquare.bottom_lt .lowerRight)) :=
  (dg_coherent_grid_square k R C Q nodes eq .lowerRight).boundary

example (R : CoherentIndexModel k GridIndex) (C : DGCat k) (Q : CoherentDiagram R C)
    (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    (s : SmallSquare) :
    (dg_coherent_grid_square k R C Q nodes eq s).square.cell = squareCell Q nodes eq s :=
  rfl

example (R : CoherentIndexModel k GridIndex) (C : DGCat k) (Q : CoherentDiagram R C)
    (nodes : GridIndex → DGDerivedModules k C)
    (eq : ∀ q : GridIndex, Q.toEnrichedFunctor.obj (R.objects.symm q) = (nodes q).obj)
    (s : SmallSquare) :
    (dg_coherent_grid_square k R C Q nodes eq s).square.topLeft = nodes s.topLeft :=
  rfl

end MathlibExtTest.AlgebraicGeometry.DGRelativeCYDiagramLedgerDgCoherentGridSquare
