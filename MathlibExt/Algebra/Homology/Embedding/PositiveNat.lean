/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.ChainComplexKernelTail

/-!
# Global inference for the positive chain embedding

The canonical `ChainComplex.kernelTailEmbedding`, `n ↦ n+1`, preserves and
reflects differential relations. Its positive image is closed under incoming
chain differentials. These global instances expose those properties on `down ℕ`.
-/

@[expose] public section
set_option autoImplicit false

namespace ComplexShape

/-- The canonical positive chain embedding preserves and reflects adjacent relations. -/
instance instIsRelIffPositiveNatEmbedding :
    ChainComplex.kernelTailEmbedding.IsRelIff :=
  instIsRelIffEmbeddingDown'Add (1 : ℕ) 1

/-- The positive image of the canonical chain embedding is incoming-closed. -/
instance instIsTruncLEPositiveNatEmbedding :
    ChainComplex.kernelTailEmbedding.IsTruncLE :=
  instIsTruncLEEmbeddingDown'Add (1 : ℕ) 1

end ComplexShape
