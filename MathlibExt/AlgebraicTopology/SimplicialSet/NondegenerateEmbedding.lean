/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.AlgebraicTopology.SimplicialSet.Degenerate
public import Mathlib.AlgebraicTopology.SimplicialSet.Monomorphisms

/-!
# Embeddings of nondegenerate simplices

A simplicial monomorphism `f : X ⟶ Y` induces a function embedding from
the nondegenerate `n`-simplices of `X` to those of `Y`. Its underlying map
is the degree-`n` component of `f`, and the associated computation lemma
is definitional.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet

variable {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (n : ℕ)

/-- For a simplicial monomorphism `f : X ⟶ Y`, the induced map on `n`-dimensional
nondegenerate simplices, as a `Function.Embedding`. -/
def nonDegenerateEmbeddingOfMono : X.nonDegenerate n ↪ Y.nonDegenerate n where
  toFun x := ⟨f.app _ x.1, (nonDegenerate_iff_of_mono f x.1).mpr x.2⟩
  inj' a b h := Subtype.ext (show a.1 = b.1 from
    (mono_iff_injective _).mp inferInstance (congrArg Subtype.val h))

@[simp]
lemma nonDegenerateEmbeddingOfMono_apply (x : X.nonDegenerate n) :
    (nonDegenerateEmbeddingOfMono f n x).val = f.app _ x.val := rfl

end SSet
