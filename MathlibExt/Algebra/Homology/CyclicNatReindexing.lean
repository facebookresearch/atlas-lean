/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
/-
Modifications copyright (c) 2026 Meta Platforms, Inc. and affiliates.
-/
/-
Ported from TauCetiProject/TauCeti at
62bbc0596dc3539d488232e4e924a338548ea0a9:
TauCeti/Algebra/Homology/Embedding/UpNatAdd.lean
Public source: https://github.com/TauCetiProject/TauCeti
The original contributors' copyright, author and Apache License 2.0
notice is retained above. Modification notice: use the explicitly
listed MathlibExt ports for this complete SBI dependency closure;
retain the mathematical declarations and original names. Identity-scalar
multilinear maps and endomorphism-application lemmas use the pinned
Mathlib API; the finite-coordinate port keeps only its four needed lemmas.
-/
module

public import Mathlib.Algebra.Homology.Embedding.Basic

/-!
# The embedding `n ↦ n + k` of `ComplexShape.up ℕ`

Extending a cochain complex indexed by `ℕ` along the embedding `n ↦ n + k` of `ComplexShape.up ℕ`
into itself places it `k` degrees higher, with zero objects in the degrees below `k`. This is
Mathlib's `ComplexShape.embeddingUp'Add 1 k`, restated for the shape `ComplexShape.up ℕ`
(definitionally `ComplexShape.up' 1`) so that it applies to `CochainComplex C ℕ` and its instances
are found there.

## Main definitions

* `ComplexShape.embeddingUpNatAdd`: the embedding `n ↦ n + k` of `ComplexShape.up ℕ`.
-/

public section

namespace ComplexShape

/-- The embedding `n ↦ n + k` of `ComplexShape.up ℕ` into itself: Mathlib's
`ComplexShape.embeddingUp'Add 1 k`, since `ComplexShape.up ℕ` unfolds to `up' 1`. -/
def embeddingUpNatAdd (k : ℕ) : (ComplexShape.up ℕ).Embedding (ComplexShape.up ℕ) :=
  embeddingUp'Add (1 : ℕ) k

@[simp] lemma embeddingUpNatAdd_f (k n : ℕ) : (embeddingUpNatAdd k).f n = n + k := (rfl)

instance (k : ℕ) : (embeddingUpNatAdd k).IsRelIff :=
  inferInstanceAs (embeddingUp'Add (1 : ℕ) k).IsRelIff

instance (k : ℕ) : (embeddingUpNatAdd k).IsTruncGE :=
  inferInstanceAs (embeddingUp'Add (1 : ℕ) k).IsTruncGE

end ComplexShape
