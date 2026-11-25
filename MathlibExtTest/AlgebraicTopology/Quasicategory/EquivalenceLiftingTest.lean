/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import MathlibExt.AlgebraicTopology.Quasicategory.EquivalenceLifting

/-!
# Public clients for strict equivalence-edge lifting

The identity constructor works on an arbitrary simplicial set. The
projection client transports the returned endpoint equality and obtains
equality of the actual typed edges, with the chosen source preserved.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory Opposite
open scoped Simplicial

universe u

namespace MathlibExtTest.AlgebraicTopology.Quasicategory.EquivalenceLiftingTest

/-- The characteristic interface constructs strict lifting for identity
maps without quasicategory or model assumptions. -/
theorem identity_hasStrictEquivalenceLifting (X : SSet.{u}) :
    SSet.HasStrictEquivalenceLifting (𝟙 X) := by
  apply (SSet.hasStrictEquivalenceLifting_iff _).mpr
  intro x₀ y₁ g hg
  exact ⟨y₁, rfl, g, hg, rfl⟩

/-- Retaining the endpoint equality allows comparison of actual typed
edges after transport, rather than only their homotopy classes. -/
theorem exists_lift_with_edge_eq {X Y : SSet.{u}} (p : X ⟶ Y)
    [SSet.HasStrictEquivalenceLifting p] {x₀ : X _⦋0⦌} {y₁ : Y _⦋0⦌}
    (g : SSet.Edge (p.app (op ⦋0⦌) x₀) y₁) (hg : g.IsEquivalence) :
    ∃ (x₁ : X _⦋0⦌) (hx₁ : p.app (op ⦋0⦌) x₁ = y₁) (f : SSet.Edge x₀ x₁),
      f.IsEquivalence ∧ (f.map p).ofEq rfl hx₁ = g := by
  obtain ⟨x₁, hx₁, f, hf, hfg⟩ :=
    SSet.HasStrictEquivalenceLifting.exists_lift (p := p) g hg
  exact ⟨x₁, hx₁, f, hf, SSet.Edge.ext hfg⟩

end MathlibExtTest.AlgebraicTopology.Quasicategory.EquivalenceLiftingTest
