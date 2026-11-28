/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


module

public import MathlibExt.Algebra.Homology.InitialSegmentShape
public import MathlibExt.Algebra.Homology.Embedding.StupidTruncNested

/-!
# Finite initial cochain intervals

The cochain shape on `Fin (q+1)` and its inclusion into the natural cochain shape
are obtained by reversing the canonical chain initial segment. Its range is
`{0,…,q}`, and the ranges increase with the endpoint.
-/

@[expose] public section

namespace ComplexShape.NatInitialInterval

/-- The ordinary cochain successor shape on the finite interval `{0,…,q}`. -/
abbrev upShape (q : ℕ) := (ComplexShape.downNatInitialSegment q).symm

/-- Include the finite cochain interval into the natural cochain shape by `Fin.val`. -/
abbrev upEmbedding (q : ℕ) : (upShape q).Embedding (ComplexShape.up ℕ) :=
  (ComplexShape.embeddingDownNatInitialSegment q).op

instance upEmbedding_isRelIff (q : ℕ) : (upEmbedding q).IsRelIff := inferInstance
instance upEmbedding_isTruncLE (q : ℕ) : (upEmbedding q).IsTruncLE := inferInstance

/-- The range of the finite cochain inclusion is exactly the degrees at most `q`. -/
theorem upEmbedding_range (q i : ℕ) :
    i ∈ Set.range (upEmbedding q).f ↔ i ≤ q :=
  ComplexShape.mem_range_embeddingDownNatInitialSegment_iff q i

/-- Inclusion of the initial interval with endpoint `p` into the range with endpoint `q`. -/
theorem upRangeLE {p q : ℕ} (h : p ≤ q) :
    (upEmbedding p).RangeLE (upEmbedding q) := by
  intro i hi
  exact (upEmbedding_range q i).2 ((upEmbedding_range p i).1 hi |>.trans h)

end ComplexShape.NatInitialInterval
