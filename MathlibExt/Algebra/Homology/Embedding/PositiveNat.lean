/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Basic

/-!
# The positive embedding of nonnegative chain indices

The embedding `n ↦ n + 1` identifies nonnegative chain degrees with the
positive degrees. It reflects the differential relation, and its image is
closed under incoming differentials. The module specializes these shape
properties to `ComplexShape.down ℕ`.
-/

@[expose] public section
set_option autoImplicit false

namespace ComplexShape

/-- The actual native positive embedding, with both nonnegative chain shapes fixed. -/
abbrev positiveNatEmbedding : (down ℕ).Embedding (down ℕ) :=
  embeddingDown'Add (1 : ℕ) 1

/-- Relation inference for the positive embedding with the standard `down ℕ` shape.
Mathlib's native instance has a `down' 1` shape head. Under the pinned typeclass
transparency, it does not match this explicitly `down ℕ`-typed goal. This bridge
reuses the native proof and supports ordinary `ChainComplex C ℕ` callers. -/
instance instIsRelIffPositiveNatEmbedding :
    positiveNatEmbedding.IsRelIff :=
  instIsRelIffEmbeddingDown'Add (1 : ℕ) 1

/-- Truncation inference for the same standard-chain shape.
The native `down' 1` provider is reused, but a direct `down ℕ` instance search
fails without this specialization. Keeping it preserves native coordinate-map
inference in clients without extra hypotheses or transparency attributes. -/
instance instIsTruncLEPositiveNatEmbedding :
    positiveNatEmbedding.IsTruncLE :=
  instIsTruncLEEmbeddingDown'Add (1 : ℕ) 1

/-- The positive embedding shifts each index by one. -/
theorem positiveNatEmbedding_f (i : ℕ) : positiveNatEmbedding.f i = i + 1 :=
  embeddingDown'Add_f 1 1 i

/-- The first selected positive degree is one. -/
theorem positiveNatEmbedding_f_zero : positiveNatEmbedding.f 0 = 1 := by
  simp

/-- The next selected positive degree is two. -/
theorem positiveNatEmbedding_f_one : positiveNatEmbedding.f 1 = 2 := by
  simp

end ComplexShape
