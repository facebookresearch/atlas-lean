/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import Mathlib.Algebra.Homology.Embedding.Basic
public import MathlibExt.Algebra.Homology.Embedding.StupidTruncNested

/-!
# Finite initial chain and cochain intervals

Fin(q+1) represents the finite interval {0,…,q}, with its ordinary successor
relation rather than a cyclic wraparound. Inclusion by natural value gives
chain and cochain shape embeddings whose ranges increase with q.
-/

@[expose] public section

namespace ComplexShape.NatInitialInterval

/--
For q∈ℕ, the downward shape on Fin(q+1) allows i→j exactly when j.val+1=i.val. It represents
the finite linear chain interval {0,…,q} without a wraparound edge.
-/
def downShape (q : ℕ) : ComplexShape (Fin (q + 1)) where
  Rel i j := j.val + 1 = i.val
  next_eq := by intro i j k hj hk; apply Fin.ext; omega
  prev_eq := by intro i j k hi hj; apply Fin.ext; omega

/--
For q∈ℕ, the finite chain interval with indices Fin(q+1) and relation j.val+1=i.val embeds in
the downward shape on ℕ by i↦i.val. Its range is {0,…,q}.
-/
def downEmbedding (q : ℕ) : (downShape q).Embedding (ComplexShape.down ℕ) where
  f := Fin.val
  injective_f := Fin.val_injective
  rel h := h

instance downEmbedding_isRelIff (q : ℕ) : (downEmbedding q).IsRelIff where
  rel' _ _ h := h

/--
For the downward interval embedding Fin(q+1)→ℕ, the range {0,…,q} is closed under outgoing
chain differentials: if j+1=i and i≤q, then j≤q. Thus the embedding satisfies IsTruncGE.
-/
instance downEmbedding_isTruncGE (q : ℕ) : (downEmbedding q).IsTruncGE where
  toIsRelIff := inferInstance
  mem_next {i j} h := by
    change j + 1 = i.val at h
    exact ⟨⟨j, by omega⟩, rfl⟩

/--
For q∈ℕ, reversing the finite downward interval gives a cochain shape on Fin(q+1) with
relation i.val+1=j.val. There is no wraparound differential.
-/
abbrev upShape (q : ℕ) := (downShape q).symm

/--
For q∈ℕ, the finite cochain interval Fin(q+1), with relation i.val+1=j.val, embeds into the
upward shape on ℕ by natural value. Its range is {0,…,q}.
-/
abbrev upEmbedding (q : ℕ) : (upShape q).Embedding (ComplexShape.up ℕ) :=
  (downEmbedding q).op

instance upEmbedding_isRelIff (q : ℕ) : (upEmbedding q).IsRelIff where
  rel' _ _ h := h

instance upEmbedding_isTruncLE (q : ℕ) : (upEmbedding q).IsTruncLE where
  toIsRelIff := inferInstance
  mem_prev {i j} h := by
    change i + 1 = j.val at h
    exact ⟨⟨i, by omega⟩, rfl⟩

theorem downEmbedding_range (q i : ℕ) :
    i ∈ Set.range (downEmbedding q).f ↔ i ≤ q := by
  constructor
  · rintro ⟨j, rfl⟩
    exact Nat.le_of_lt_succ j.isLt
  · intro h
    exact ⟨⟨i, by omega⟩, rfl⟩

theorem upEmbedding_range (q i : ℕ) :
    i ∈ Set.range (upEmbedding q).f ↔ i ≤ q := downEmbedding_range q i

/--
For natural cutoffs p≤q, the range of the downward embedding Fin(p+1)→ℕ is contained in the
range of Fin(q+1)→ℕ, with each finite index retaining its natural value.
-/
theorem downRangeLE {p q : ℕ} (h : p ≤ q) :
    (downEmbedding p).RangeLE (downEmbedding q) := by
  intro i hi
  exact (downEmbedding_range q i).2 ((downEmbedding_range p i).1 hi |>.trans h)

/--
For natural cutoffs p≤q, the upward interval embedding with range {0,…,p} has its range
contained in the upward interval with range {0,…,q}.
-/
theorem upRangeLE {p q : ℕ} (h : p ≤ q) :
    (upEmbedding p).RangeLE (upEmbedding q) := downRangeLE h

end ComplexShape.NatInitialInterval
