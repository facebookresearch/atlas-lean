/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.VertexCoverKernel

@[expose] public section

/-- The empty graph has the empty cover, and the rule is vacuous. -/
example : (⊥ : SimpleGraph (Fin 2)).IsVertexCover (↑(∅ : Finset (Fin 2))) := by
  simp

end
