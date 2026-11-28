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
# Nondegenerate simplices under monomorphisms

Let `f : X ⟶ Y` be a monomorphism of simplicial sets in universe `u`. For every `n : ℕ`, a
simplex of `X` is nondegenerate exactly when its image under `f` is nondegenerate. The
injective map on `n`-simplices therefore restricts to an embedding `X.nonDegenerate n ↪
Y.nonDegenerate n`.
-/

@[expose] public section

universe u

open CategoryTheory Opposite Simplicial SimplexCategory

namespace SSet

variable {X Y : SSet.{u}} (f : X ⟶ Y) [Mono f] (n : ℕ)

/-- For simplicial sets `X, Y : SSet.{u}`, a monomorphism `f : X ⟶ Y`, and `n : ℕ`, the embedding
`X.nonDegenerate n ↪ Y.nonDegenerate n` sends `x` to the simplex `f.app _ x`. Monomorphisms
preserve and reflect nondegeneracy, and their maps on simplices are injective. -/
def nonDegenerateEmbeddingOfMono : X.nonDegenerate n ↪ Y.nonDegenerate n where
  toFun x := ⟨f.app _ x.1, (nonDegenerate_iff_of_mono f x.1).mpr x.2⟩
  inj' a b h := Subtype.ext (show a.1 = b.1 from
    (mono_iff_injective _).mp inferInstance (congrArg Subtype.val h))

@[simp]
lemma nonDegenerateEmbeddingOfMono_apply (x : X.nonDegenerate n) :
    (nonDegenerateEmbeddingOfMono f n x).val = f.app _ x.val := rfl

end SSet
