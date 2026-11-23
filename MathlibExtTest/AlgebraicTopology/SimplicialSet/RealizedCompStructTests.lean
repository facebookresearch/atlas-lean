/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct

@[expose] public section

/-!
# Realized composition structure consumer tests

Focused downstream checks for the public `SSet.realizedCompStructHomotopic`
API: exact universe-polymorphic signature, direct-edge-first orientation, outer
endpoints, and usability with `SSet.Edge.CompStruct.idComp` and `compId`.
Uses only public declarations; does not unfold the proof and claims only
`Path.Homotopic`, never strict path equality. Covers identity-edge null-homotopy
via `SSet.realizedEdgePath_id_homotopic`.
-/

set_option autoImplicit false

open CategoryTheory Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.SimplicialSet.RealizedCompStructTests

/-- Universe-polymorphic signature with direct-edge-first orientation. -/
example {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂) :
    (TopCat.pathEquiv (SSet.realizedEdgePath e₀₂)).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath e₀₁)).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath e₁₂))) :=
  SSet.realizedCompStructHomotopic h

/-- Degenerate left-identity composition is usable. -/
example {X : SSet.{0}} {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    (TopCat.pathEquiv (SSet.realizedEdgePath e)).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id x₀))).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath e))) :=
  SSet.realizedCompStructHomotopic (SSet.Edge.CompStruct.idComp e)

/-- Degenerate right-identity composition is usable. -/
example {X : SSet.{0}} {x₀ x₁ : X _⦋0⦌} (e : X.Edge x₀ x₁) :
    (TopCat.pathEquiv (SSet.realizedEdgePath e)).Homotopic
      ((TopCat.pathEquiv (SSet.realizedEdgePath e)).trans
        (TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id x₁)))) :=
  SSet.realizedCompStructHomotopic (SSet.Edge.CompStruct.compId e)

/-- Realized identity edge path is null-homotopic. -/
example {X : SSet.{u}} (x : X _⦋0⦌) :
    (TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id x))).Homotopic
      (Path.refl (SSet.realizedVertex x)) :=
  SSet.realizedEdgePath_id_homotopic x

end MathlibExtTest.AlgebraicTopology.SimplicialSet.RealizedCompStructTests

end
