/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.CoherentIso

/-! # Vertices of the coherent-isomorphism interval: tests

Public clients exercise `SSet.coherentIso.vertexBool` and the
thinness extensionality `SSet.coherentIso.eq_of_forall_vertexBool_eq`
through the neutral companion module
`MathlibExt.AlgebraicTopology.SimplicialSet.CoherentIso` only.
-/

@[expose] public section

open CategoryTheory Opposite SimplexCategory.Truncated

open scoped Simplicial SimplicialObject.Truncated

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet
namespace CoherentIsoTest

#check @SSet.coherentIso.vertexBool
#check @SSet.coherentIso.eq_of_forall_vertexBool_eq

section VertexBool

/-- The source vertex of `coherentIso` has vertex boolean
`false`. -/
example : SSet.coherentIso.vertexBool SSet.coherentIso.x₀.{u} 0 = false := rfl

/-- The target vertex of `coherentIso` has vertex boolean
`true`. -/
example : SSet.coherentIso.vertexBool SSet.coherentIso.x₁.{u} 0 = true := rfl

/-- The forward edge of `coherentIso` has vertex pattern
`false, true`. -/
example : SSet.coherentIso.vertexBool SSet.coherentIso.hom.edge 0 = false ∧
    SSet.coherentIso.vertexBool SSet.coherentIso.hom.edge 1 = true := ⟨rfl, rfl⟩

/-- The backward edge of `coherentIso` has vertex pattern
`true, false`. -/
example : SSet.coherentIso.vertexBool SSet.coherentIso.inv.edge 0 = true ∧
    SSet.coherentIso.vertexBool SSet.coherentIso.inv.edge 1 = false := ⟨rfl, rfl⟩

/-- The triangle `coherentIso.homInvId` has vertex pattern
`false, true, false`. -/
example : SSet.coherentIso.vertexBool SSet.coherentIso.homInvId.simplex 0 = false ∧
    SSet.coherentIso.vertexBool SSet.coherentIso.homInvId.simplex 1 = true ∧
    SSet.coherentIso.vertexBool SSet.coherentIso.homInvId.simplex 2 = false :=
  ⟨rfl, rfl, rfl⟩

/-- Thinness extensionality applied reflexively. -/
example {n : ℕ} (s : SSet.coherentIso.{u} _⦋n⦌) : s = s :=
  SSet.coherentIso.eq_of_forall_vertexBool_eq (fun _ ↦ rfl)

/-- Thinness extensionality recovers the forward edge from its
vertex pattern. -/
example (s : SSet.coherentIso.{u} _⦋1⦌)
    (h0 : SSet.coherentIso.vertexBool s 0 = false)
    (h1 : SSet.coherentIso.vertexBool s 1 = true) :
    s = SSet.coherentIso.hom.edge :=
  SSet.coherentIso.eq_of_forall_vertexBool_eq (fun i ↦ by
    fin_cases i
    · exact h0
    · exact h1)

end VertexBool

end CoherentIsoTest
end MathlibExtTest.AlgebraicTopology.SimplicialSet
