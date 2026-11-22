/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalCylinderBoundary
import MathlibExt.AlgebraicTopology.SimplicialSet.Marked.IntervalCylinderPullbacks

/-!
# Actual original-universe exactness of the native marked interval cylinder

The existing marked product/internal-Hom adjunction preserves all
original-universe colimits. The proved original boundary monomorphism,
product-map monicity and actual endpoint pullbacks supply every native
exactness field. No model, anodyne-system or outcome premise is assumed.
-/

noncomputable section
universe u
open CategoryTheory Limits HomotopicalAlgebra
open scoped Simplicial

namespace SSet.Marked

/-- The native precylinder endpoint is exactly its same original marked interval endpoint. -/
theorem intervalCylinder_endpoint (X : Marked.{u}) (ε : Fin 2) :
    (intervalCylinder.{u}.app X).endpoint ε = intervalCylinderEndpoint X ε := by
  fin_cases ε <;> rfl

/-- The native original marked interval cylinder is exact at the original working universe. -/
theorem intervalCylinder_isExact : intervalCylinder.{u}.IsExact.{u} := by
  let _ : Functor.PreservesMonomorphisms intervalCylinder.{u}.I := ⟨fun f => intervalCylinder_map_mono f⟩
  let _ : PreservesColimitsOfSize.{u, u} intervalCylinder.{u}.I := intervalCylinder_preservesColimits
  refine
    { mono_boundary := intervalCylinder_boundary_mono
      endpoint_isPullback := ?_ }
  intro X Y f _ ε
  rw [intervalCylinder_endpoint, intervalCylinder_endpoint]
  exact intervalCylinderEndpoint_isPullback f ε

end SSet.Marked
