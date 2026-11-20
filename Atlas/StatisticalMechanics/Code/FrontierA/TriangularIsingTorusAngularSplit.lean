/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Code.FrontierA.TriangularIsingTorusHomology
import Code.FrontierA.KacWardPortChainHomology





namespace StatMech.FrontierA




theorem triangularTorus_orderedSplit_surfaceQuadraticEvenPolynomial_eq
    (L : Nat) [Fact (2 < L)]
    (order : KWPortOrder (triangularTorusGraph L))
    (weight : Sym2 (ZMod L × ZMod L) → Complex) (a b : Fin 2) :
    surfaceQuadraticEvenPolynomial
        (kwOrderedDartPortSplitGraph (triangularTorusGraph L) order)
        (kwOrderedSplitEdgeClass (triangularTorusSurfaceEdgeClass L))
        (triangularTorusSurfaceSpin a b)
        (kwOrderedSplitWeight (triangularTorusGraph L) weight) =
      triangularTorusWeightedSpinCharacterSum L weight a b := by
  rw [kwOrderedSplit_surfaceQuadraticEvenPolynomial_eq
    (triangularTorusGraph L) order (triangularTorusSurfaceEdgeClass L)
    (triangularTorusSurfaceEdgeClass_diag L)
    (triangularTorusSurfaceSpin a b) weight]
  exact triangularTorus_surfaceQuadraticEvenPolynomial_eq L weight a b

end StatMech.FrontierA
