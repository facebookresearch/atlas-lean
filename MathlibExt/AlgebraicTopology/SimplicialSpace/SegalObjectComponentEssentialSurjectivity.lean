/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import MathlibExt.AlgebraicTopology.SimplicialSpace.SegalHoEssentialSurjectivity

/-!
# Component surjectivity from vertex surjectivity

A simplicial map that is surjective on vertices induces a surjection on simplicial components.
The proof uses vertex representatives of component classes and applies to arbitrary simplicial
sets, including empty ones.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
universe u
open CategoryTheory Opposite
open scoped Simplicial

namespace SSet

/-- Surjectivity on original vertices covers all original simplicial components,
including empty endpoints and every value universe. -/
theorem mapPiZero_surjective_of_surjective_vertices
    {X Y : SSet.{u}} (f : X ⟶ Y)
    (hv : Function.Surjective (f.app (op ⦋0⦌))) :
    Function.Surjective (SSet.mapπ₀ f) := by
  intro q
  obtain ⟨y, hy⟩ := SSet.π₀.mk_surjective q
  obtain ⟨x, hx⟩ := hv y
  refine ⟨SSet.π₀.mk x, ?_⟩
  rw [SSet.mapπ₀_mk, hx, hy]

end SSet
