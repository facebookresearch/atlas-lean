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

The embedding that defines a topological pair is a monomorphism in TopCat. This
follows from injectivity of an embedding and the characterization of
monomorphisms in TopCat by injective underlying maps.
-/

@[expose] public section

open CategoryTheory

universe u

namespace TopPair

/-- The embedding in a topological pair is a monomorphism. -/
instance (P : TopPair.{u}) : Mono P.map :=
  (TopCat.mono_iff_injective P.map).2 P.isEmbedding_map.injective

end TopPair
