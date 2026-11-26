/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Basic

/-!
# Positive degrees of nonnegative chain complexes

The embedding e(n)=n+1 of the downward natural shape has image the positive
degrees. It preserves and reflects adjacent relations, and its image is
closed under incoming chain differentials.
-/

@[expose] public section
set_option autoImplicit false

namespace ComplexShape

/--
For the downward shape on ℕ, with differential relation j+1=i, e(n)=n+1 embeds the shape into
itself. Its image is exactly the positive natural degrees.
-/
abbrev positiveNatEmbedding : (down ℕ).Embedding (down ℕ) :=
  embeddingDown'Add (1 : ℕ) 1

/-
This instance specializes the native down' 1 relation proof to the down ℕ shape head.
-/

/-
This specializes the native down' 1 relation instance to the down ℕ shape head.
-/

/--
For e(n)=n+1 in the downward natural shape, j+1=i holds exactly when e(j)+1=e(i). Thus the
positive-degree embedding preserves and reflects differential relations.
-/
instance instIsRelIffPositiveNatEmbedding :
    positiveNatEmbedding.IsRelIff :=
  instIsRelIffEmbeddingDown'Add (1 : ℕ) 1

/-
The native truncation instance is specialized to the down ℕ shape to preserve instance inference.
-/

/-
The native truncation instance is specialized to the down ℕ shape for instance inference.
-/

/--
For e(n)=n+1 in the downward natural shape, every incoming differential to an image degree
starts in the image: a relation m→e(n) has m=e(n)+1>0. This is the IsTruncLE property of the
positive embedding.
-/
instance instIsTruncLEPositiveNatEmbedding :
    positiveNatEmbedding.IsTruncLE :=
  instIsTruncLEEmbeddingDown'Add (1 : ℕ) 1

/--
For every i∈ℕ, the positive chain-degree embedding e has index formula e(i)=i+1.
-/
theorem positiveNatEmbedding_f (i : ℕ) : positiveNatEmbedding.f i = i + 1 :=
  embeddingDown'Add_f 1 1 i

/--
For the positive-degree embedding e(n)=n+1 of downward natural shapes, e(0)=1. Restricted
degree zero therefore selects original chain degree one.
-/
theorem positiveNatEmbedding_f_zero : positiveNatEmbedding.f 0 = 1 := by
  simp

/--
For the positive-degree embedding e(n)=n+1, e(1)=2. Restricted degree one selects original
chain degree two.
-/
theorem positiveNatEmbedding_f_one : positiveNatEmbedding.f 1 = 2 := by
  simp

end ComplexShape
