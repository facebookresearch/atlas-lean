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
# Finite initial intervals of nonnegative complex shapes

The finite chain indices use the natural-number successor relation. The
chain embedding has image closed under outgoing differentials, and the
opposite cochain embedding has image closed under incoming differentials.
There is no differential from the last index to the first.
-/

@[expose] public section

namespace ComplexShape.NatInitialInterval

/-- The original downward natural successor relation on the finite interval. -/
def downShape (q : ℕ) : ComplexShape (Fin (q + 1)) where
  Rel i j := j.val + 1 = i.val
  next_eq := by intro i j k hj hk; apply Fin.ext; omega
  prev_eq := by intro i j k hi hj; apply Fin.ext; omega

/-- The finite chain interval is embedded by its original natural value. -/
def downEmbedding (q : ℕ) : (downShape q).Embedding (ComplexShape.down ℕ) where
  f := Fin.val
  injective_f := Fin.val_injective
  rel h := h

instance downEmbedding_isRelIff (q : ℕ) : (downEmbedding q).IsRelIff where
  rel' _ _ h := h

/-- Original chain differentials cannot leave a finite initial interval. -/
instance downEmbedding_isTruncGE (q : ℕ) : (downEmbedding q).IsTruncGE where
  toIsRelIff := inferInstance
  mem_next {i j} h := by
    change j + 1 = i.val at h
    exact ⟨⟨j, by omega⟩, rfl⟩

/-- The finite cochain shape, with the original finite indices and reversed relation. -/
abbrev upShape (q : ℕ) := (downShape q).symm

/-- The cochain interval has the same original indices and the reversed relation. -/
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

/-- Initial chain supports increase with the original cutoff. -/
theorem downRangeLE {p q : ℕ} (h : p ≤ q) :
    (downEmbedding p).RangeLE (downEmbedding q) := by
  intro i hi
  exact (downEmbedding_range q i).2 ((downEmbedding_range p i).1 hi |>.trans h)

/-- Initial cochain supports increase with the original cutoff. -/
theorem upRangeLE {p q : ℕ} (h : p ≤ q) :
    (upEmbedding p).RangeLE (upEmbedding q) := downRangeLE h

end ComplexShape.NatInitialInterval
