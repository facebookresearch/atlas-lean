/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Basic

/-!
# Noncyclic initial segments of the natural chain-complex shape

The standard additive structure on `Fin (p + 1)` is cyclic, so
`ComplexShape.down (Fin (p + 1))` has an unwanted wraparound differential.
This file defines instead the shape obtained by restricting
`ComplexShape.down ℕ` to the initial segment `0, ..., p`, together with its
canonical truncation embedding and the embeddings between nested segments.
-/

@[expose] public section

set_option autoImplicit false
set_option warningAsError true

namespace ComplexShape

/-- The noncyclic restriction of `ComplexShape.down ℕ` to degrees at most
`p`. -/
def downNatInitialSegment (p : ℕ) : ComplexShape (Fin (p + 1)) where
  Rel i j := j.1 + 1 = i.1
  next_eq h h' := Fin.ext (Nat.add_right_cancel (h.trans h'.symm))
  prev_eq h h' := Fin.ext (h.symm.trans h')

@[simp]
theorem downNatInitialSegment_rel_iff (p : ℕ) (i j : Fin (p + 1)) :
    (downNatInitialSegment p).Rel i j ↔ j.1 + 1 = i.1 :=
  Iff.rfl

/-- Embed the noncyclic initial segment through degree `p` into the natural
chain-complex shape. -/
def embeddingDownNatInitialSegment (p : ℕ) :
    (downNatInitialSegment p).Embedding (ComplexShape.down ℕ) :=
  Embedding.mk' _ _ (fun i => i.1) (fun _ _ h => Fin.ext h) fun _ _ => Iff.rfl

instance (p : ℕ) : (embeddingDownNatInitialSegment p).IsRelIff where
  rel' _ _ h := h

/-- The initial segment is stable under the next differential of a chain
complex, so it is a lower-degree stupid truncation shape. -/
instance (p : ℕ) : (embeddingDownNatInitialSegment p).IsTruncGE where
  mem_next {j k'} h := by
    have hk' : k' < p + 1 := by
      calc
        k' < k' + 1 := Nat.lt_succ_self k'
        _ = j.1 := h
        _ < p + 1 := j.2
    exact ⟨⟨k', hk'⟩, rfl⟩

/-- A natural degree lies in the initial-segment embedding exactly when it is
at most the endpoint. -/
theorem mem_range_embeddingDownNatInitialSegment_iff (p n : ℕ) :
    (∃ i, (embeddingDownNatInitialSegment p).f i = n) ↔ n ≤ p := by
  constructor
  · rintro ⟨i, rfl⟩
    change i.val ≤ p
    omega
  · intro hn
    exact ⟨⟨n, by omega⟩, rfl⟩

/-- Embed the initial segment through `p` into a larger initial segment
through `p'`. -/
def downNatInitialSegmentEmbedding {p p' : ℕ} (h : p ≤ p') :
    (downNatInitialSegment p).Embedding (downNatInitialSegment p') :=
  Embedding.mk' _ _
    (fun i => Fin.castLE (Nat.succ_le_succ h) i)
    (fun _ _ hij => Fin.ext
      (congrArg (fun z : Fin (p' + 1) => z.val) hij))
    (fun _ _ => Iff.rfl)

instance {p p' : ℕ} (h : p ≤ p') :
    (downNatInitialSegmentEmbedding h).IsRelIff where
  rel' _ _ h := h

/-- Nested initial segments are again stable under the next differential. -/
instance {p p' : ℕ} (h : p ≤ p') :
    (downNatInitialSegmentEmbedding h).IsTruncGE where
  mem_next {j k'} hrel := by
    have hk' : k'.1 < p + 1 := by
      calc
        k'.1 < k'.1 + 1 := Nat.lt_succ_self k'.1
        _ = j.1 := hrel
        _ < p + 1 := j.2
    exact ⟨⟨k'.1, hk'⟩, Fin.ext rfl⟩

/-- The nested segment embedding commutes strictly with the embeddings into
natural degrees. -/
@[simp]
theorem downNatInitialSegmentEmbedding_f_embedding_f
    {p p' : ℕ} (h : p ≤ p') (i : Fin (p + 1)) :
    (embeddingDownNatInitialSegment p').f
        ((downNatInitialSegmentEmbedding h).f i) =
      (embeddingDownNatInitialSegment p).f i :=
  rfl

end ComplexShape

end
