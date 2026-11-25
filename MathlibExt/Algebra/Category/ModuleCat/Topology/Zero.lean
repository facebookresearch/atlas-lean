/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

-- Author: @toskua, Avocado
module

public import Mathlib.Algebra.Category.ModuleCat.Topology.Basic

/-!
# Zero topological modules

A topological module with subsingleton carrier is a zero object.  The
result needs only a ring with an arbitrary topology: all continuity data is
already carried by the objects and the zero continuous linear maps.

This file introduces no instance and has no continuous-cohomology
dependency.

## Main declaration

* `TopModuleCat.isZero_of_subsingleton`
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace TopModuleCat

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]

/-- A topological module with subsingleton carrier is a zero object. -/
theorem isZero_of_subsingleton (M : TopModuleCat.{v} R) [Subsingleton M] :
    Limits.IsZero M where
  unique_to X := ⟨⟨⟨TopModuleCat.ofHom (0 : M →L[R] X)⟩, fun f => by
    ext x
    rw [Subsingleton.elim x (0 : M)]
    simp⟩⟩
  unique_from X := ⟨⟨⟨TopModuleCat.ofHom (0 : X →L[R] M)⟩, fun f => by
    ext x
    subsingleton⟩⟩

end TopModuleCat
