/-
Copyright (c) 2026 Tsutomu Okano. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: @toskua, Avocado
-/
module

public import MathlibExt.AlgebraicTopology.SimplicialSet.RealizedCompStruct

/-!
# Realized composition consumers under actual continuous maps

Keep the original three vertices, edge orientation and half-split path
concatenation. Apply a continuous map to the actual realized homotopy
and retain the endpoint-fixed identity-edge case.
-/

set_option autoImplicit false
set_option maxRecDepth 512

noncomputable section
universe u t

open CategoryTheory Simplicial
open scoped Simplicial unitInterval

namespace RealizedCompositionClients

example {X : SSet.{u}} {x₀ x₁ x₂ : X _⦋0⦌}
    {e₀₁ : X.Edge x₀ x₁} {e₁₂ : X.Edge x₁ x₂} {e₀₂ : X.Edge x₀ x₂}
    (h : SSet.Edge.CompStruct e₀₁ e₁₂ e₀₂)
    {T : Type t} [TopologicalSpace T] (g : C(|X|, T)) :
    ((TopCat.pathEquiv (SSet.realizedEdgePath e₀₂)).map g.continuous).Homotopic
      (((TopCat.pathEquiv (SSet.realizedEdgePath e₀₁)).map g.continuous).trans
        ((TopCat.pathEquiv (SSet.realizedEdgePath e₁₂)).map g.continuous)) := by
  have hg := (SSet.realizedCompStructHomotopic h).map g
  rw [Path.map_trans] at hg
  exact hg

example {X : SSet.{u}} (x : X _⦋0⦌)
    {T : Type t} [TopologicalSpace T] (g : C(|X|, T)) :
    ((TopCat.pathEquiv (SSet.realizedEdgePath (SSet.Edge.id x))).map g.continuous).Homotopic
      (Path.refl (g (SSet.realizedVertex x))) := by
  have hg := (SSet.realizedEdgePath_id_homotopic x).map g
  have hRefl : (Path.refl (SSet.realizedVertex x)).map g.continuous =
      Path.refl (g (SSet.realizedVertex x)) := rfl
  rw [hRefl] at hg
  exact hg

end RealizedCompositionClients
