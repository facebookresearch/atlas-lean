/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: @toskua
-/
module

public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.Basic

/-!
# Closed linear orbits of arbitrary bounded-operator sets

The carrier is the norm closure of the complex span of the literal images
of the original vector. An operator set need not be an algebra, be unital,
or be closed. The ambient complex normed space need not be a Hilbert space
or be complete. The subtype-range and set-image presentations have exactly
the same generators.
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace ContinuousLinearMap

noncomputable section

universe u v

variable {H : Type u} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- Let `H` be a normed complex vector space and let `ξ ∈ H`. The operator set consists of
continuous complex-linear endomorphisms of `H`, and closure is for the norm topology.

The norm-closed complex linear orbit of a vector under an arbitrary operator set. -/
def orbitSubspace (S : Set (H →L[ℂ] H)) (ξ : H) : Submodule ℂ H :=
  (Submodule.span ℂ (Set.range fun T : S => (T : H →L[ℂ] H) ξ)).topologicalClosure

/-- Let `H` be a normed complex vector space and let `ξ ∈ H`. The operator set consists of
continuous complex-linear endomorphisms of `H`, and closure is for the norm topology.

The subtype-range carrier is exactly the closure of the span of the set image. -/
theorem orbitSubspace_eq_span_image (S : Set (H →L[ℂ] H)) (ξ : H) :
    orbitSubspace S ξ =
      (Submodule.span ℂ ((fun T : H →L[ℂ] H => T ξ) '' S)).topologicalClosure := by
  rw [orbitSubspace, Set.image_eq_range]

/-- Let `H` be a normed complex vector space and let `ξ ∈ H`. The operator set consists of
continuous complex-linear endomorphisms of `H`, and closure is for the norm topology. The
operator family is indexed by an arbitrary type `ι`.

An operator family and its range generate the same closed orbit, with an independent universe
for the index type. -/
theorem orbitSubspace_range {ι : Type v} (T : ι → H →L[ℂ] H) (ξ : H) :
    orbitSubspace (Set.range T) ξ =
      (Submodule.span ℂ (Set.range fun i : ι => T i ξ)).topologicalClosure := by
  rw [orbitSubspace_eq_span_image, ← Set.range_comp']

end

end ContinuousLinearMap
