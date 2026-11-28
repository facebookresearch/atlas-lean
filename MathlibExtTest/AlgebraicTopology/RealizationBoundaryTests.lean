/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.AlgebraicTopology.SimplicialSet.Realization.Boundary
import MathlibExt.AlgebraicTopology.SimplicialSet.Realization.ZeroBoundary

/-! # A genuine one-dimensional boundary point and explicit zero-boundary complement maps -/

noncomputable section

open Simplicial CategoryTheory

namespace MathlibExtTest.RealizationBoundary

private def endpoint : Convexity.StdSimplex ℝ (Fin 2) :=
  Convexity.StdSimplex.single (1 : Fin 2)

example : endpoint.weights 0 = 0 := by simp [endpoint, Convexity.StdSimplex.single]

example : (⦋1⦌.toTopHomeo).symm endpoint ∈
    Set.range ⇑(SSet.toTop.map (SSet.boundary.{0} 1).ι) :=
  SSet.mem_realizedBoundary_of_zeroCoord 1 endpoint 0
    (by simp [endpoint, Convexity.StdSimplex.single])

private def zeroVertex : SSet.toTop.obj (Δ[0] : SSet.{0}) :=
  (⦋0⦌.toTopHomeo).symm (Convexity.StdSimplex.single (0 : Fin 1))

example : (SSet.realizedBoundaryZeroComplSubspaceIso.hom zeroVertex).val = zeroVertex := rfl

example (x : ↥((Set.range (SSet.toTop.map (SSet.boundary.{0} 0).ι).hom)ᶜ)) :
    SSet.realizedBoundaryZeroComplSubspaceIso.inv x = x.val := rfl

end MathlibExtTest.RealizationBoundary
