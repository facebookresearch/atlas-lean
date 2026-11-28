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
# Zero objects among topological modules

For a ring with any topology, a topological module with a subsingleton carrier is a zero
object. Its unique morphisms to and from every other object are the zero continuous linear
maps. The ring and carrier universes are independent.
-/

@[expose] public section

set_option autoImplicit false

open CategoryTheory

namespace TopModuleCat

universe u v

variable {R : Type u} [Ring R] [TopologicalSpace R]

/-- Subsingleton topological module is a zero object.

A topological `R`-module with subsingleton carrier satisfies the categorical zero-object
property. -/
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
