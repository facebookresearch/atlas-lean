/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.FieldTheory.CountableEmbeddingComplex

/-! # Consumers for embeddings of countable fields into `ℂ` -/

namespace FieldCountableEmbeddingComplexTest

universe u

/-- The exact source statement, with no added hypothesis. -/
public theorem exactSource (K : Type u) [Field K] [CharZero K]
    [Countable K] : Nonempty (K →+* ℂ) :=
  Field.nonempty_ringHom_complex_of_countable K

/-- In particular `ℚ` embeds, as it must. -/
public example : Nonempty (ℚ →+* ℂ) :=
  Field.nonempty_ringHom_complex_of_countable ℚ

end FieldCountableEmbeddingComplexTest
