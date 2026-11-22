/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Topology.Category.TopPair

/-!
# Monomorphisms in topological pairs

The embedding morphism of a topological pair is a monomorphism in `TopCat`.
Its underlying function is injective, so `TopCat.mono_iff_injective` gives
the categorical statement.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopPair

/-- The embedding in a topological pair is a monomorphism. -/
instance (P : TopPair.{u}) : Mono P.map :=
  (TopCat.mono_iff_injective P.map).2 P.isEmbedding_map.injective

end TopPair
