/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.CoherentConeOneIntervalIso

/-!
# Original endpoint and edge readbacks of the coherent interval cone

The full maximum interval map retains the original singleton source,
full two-vertex target and the original nonidentity coefficient edge.
These whole degree-zero/one readbacks determine the correct orientation
of the relative free attachment, without marking its noninvertible edge.
-/

noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet.Marked.CoherentWeight
attribute [local instance] vertexDecidableEq

/-- The original singleton source maps to the actual interval vertex zero. -/
theorem coneZeroInterval_source :
    coneZeroIntervalIso.{u}.hom.hom.app (op ⦋0⦌) (nerveEquiv.symm coefficientSource) =
      SSet.stdSimplex.obj₀Equiv.symm 0 := by
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  rfl

/-- The whole original full two-vertex cone target maps to the actual interval vertex one. -/
theorem coneZeroInterval_target :
    coneZeroIntervalIso.{u}.hom.hom.app (op ⦋0⦌) (nerveEquiv.symm coefficientTarget) =
      SSet.stdSimplex.obj₀Equiv.symm 1 := by
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i
  rfl

/-- The original nonidentity cone coefficient edge is exactly the full native interval identity simplex,
  retaining its noninvertible direction. -/
theorem coneZeroInterval_edge :
    coneZeroIntervalIso.{u}.hom.hom.app (op ⦋1⦌) coefficientEdge =
      SSet.stdSimplex.objEquiv.symm (𝟙 ⦋1⦌) := by
  apply SSet.stdSimplex.ext
  intro i
  fin_cases i <;> rfl

/-- The original coefficient edge remains unmarked under the actual whole minimum interval comparison. -/
theorem coefficientEdge_not_marked : coefficientEdge.{u} ∉ (coneWeight zeroOne).marking := by
  change ¬ coefficientSource.maximum = coefficientTarget.maximum
  exact (by decide : (ULift.up (0 : Fin 2) : Vertex.{u} 1) ≠ ULift.up 1)

end SSet.Marked.CoherentWeight
