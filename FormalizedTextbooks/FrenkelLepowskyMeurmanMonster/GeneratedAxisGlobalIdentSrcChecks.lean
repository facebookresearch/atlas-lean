/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalTwelveTwelfthIdentTri

/-! # Chunked pair checks for forward triality images

The pair check `twPairCheck` of the generic triality image (worker `gtwelfth`) evaluates
`552` rational comparisons in one kernel computation. `srcPairChunk` is one block of consecutive
pair indices of one family, and `srcTwPairCheck_of_chunks` assembles the full check from eight
blocks of `69`, each decided separately (bounded kernel memory). -/

@[expose] public noncomputable section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
open GeneratedAxisGlobalTwelveTwelfthIdent
set_option autoImplicit false

/-- One block of the pair check: the pair indices `a, …, a + n - 1` of family `s`. -/
def srcPairChunk (P' : List (ℕ × ℤ)) (L : IdentVec) (D : ℚ) (s a n : ℕ) : Bool :=
  (List.range' a n).all
    (fun p => decide (lookupQ P' (276 * s + p) / (2 * D) = twTriPairEntry L s p))

/-- The pair check from its range part and eight blocks of `69` pair indices. -/
theorem srcTwPairCheck_of_chunks (P' : List (ℕ × ℤ)) (L : IdentVec) (D : ℚ)
    (h0 : P'.all (fun q => decide (q.1 < 552)) = true)
    (h : ∀ s < 2, ∀ c < 4, srcPairChunk P' L D s (69 * c) 69 = true) :
    twPairCheck P' L D = true := by
  unfold twPairCheck
  rw [h0, Bool.true_and, List.all_eq_true]
  intro s _
  rw [List.all_eq_true]
  intro p _
  have hs := s.isLt
  have hp := p.isLt
  have hc := h s.val hs (p.val / 69) (by omega)
  unfold srcPairChunk at hc
  rw [List.all_eq_true] at hc
  exact hc p.val (List.mem_range'_1.mpr ⟨by omega, by omega⟩)

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
