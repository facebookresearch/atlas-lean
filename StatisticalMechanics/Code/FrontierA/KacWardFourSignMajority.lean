/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/




import Mathlib.Data.Real.Basic








namespace StatMech.FrontierA

theorem kw_four_signs_have_ear {s0 s1 s2 s3 : Real}
    (h0 : s0 ≠ 0) (h1 : s1 ≠ 0) (h2 : s2 ≠ 0) (h3 : s3 ≠ 0)
    (hNo02 : ¬(s0 * s3 < 0 ∧ s1 * s2 < 0))
    (hNo13 : ¬(s1 * s0 < 0 ∧ s2 * s3 < 0)) :
    (((0 < s3 ∧ 0 < s0 ∧ 0 < s2) ∨
        (s3 < 0 ∧ s0 < 0 ∧ s2 < 0)) ∨
      ((0 < s0 ∧ 0 < s1 ∧ 0 < s3) ∨
        (s0 < 0 ∧ s1 < 0 ∧ s3 < 0)) ∨
      ((0 < s1 ∧ 0 < s2 ∧ 0 < s0) ∨
        (s1 < 0 ∧ s2 < 0 ∧ s0 < 0)) ∨
      ((0 < s2 ∧ 0 < s3 ∧ 0 < s1) ∨
        (s2 < 0 ∧ s3 < 0 ∧ s1 < 0))) := by
  rcases lt_or_gt_of_ne h0 with h0n | h0p <;>
    rcases lt_or_gt_of_ne h1 with h1n | h1p <;>
    rcases lt_or_gt_of_ne h2 with h2n | h2p <;>
    rcases lt_or_gt_of_ne h3 with h3n | h3p
  · exact Or.inl (Or.inr ⟨h3n, h0n, h2n⟩)
  · exact Or.inr <| Or.inr <| Or.inl <| Or.inr ⟨h1n, h2n, h0n⟩
  · exact Or.inr <| Or.inl <| Or.inr ⟨h0n, h1n, h3n⟩
  · exact (hNo02 <|
      ⟨mul_neg_of_neg_of_pos h0n h3p,
        mul_neg_of_neg_of_pos h1n h2p⟩).elim
  · exact Or.inl (Or.inr ⟨h3n, h0n, h2n⟩)
  · exact (hNo13 <|
      ⟨mul_neg_of_pos_of_neg h1p h0n,
        mul_neg_of_neg_of_pos h2n h3p⟩).elim
  · exact (hNo13 <|
      ⟨mul_neg_of_pos_of_neg h1p h0n,
        mul_neg_of_pos_of_neg h2p h3n⟩).elim
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨h2p, h3p, h1p⟩
  · exact Or.inr <| Or.inr <| Or.inr <| Or.inr ⟨h2n, h3n, h1n⟩
  · exact (hNo13 <|
      ⟨mul_neg_of_neg_of_pos h1n h0p,
        mul_neg_of_neg_of_pos h2n h3p⟩).elim
  · exact (hNo13 <|
      ⟨mul_neg_of_neg_of_pos h1n h0p,
        mul_neg_of_pos_of_neg h2p h3n⟩).elim
  · exact Or.inl (Or.inl ⟨h3p, h0p, h2p⟩)
  · exact (hNo02 <|
      ⟨mul_neg_of_pos_of_neg h0p h3n,
        mul_neg_of_pos_of_neg h1p h2n⟩).elim
  · exact Or.inr <| Or.inl <| Or.inl ⟨h0p, h1p, h3p⟩
  · exact Or.inr <| Or.inr <| Or.inl <| Or.inl ⟨h1p, h2p, h0p⟩
  · exact Or.inl (Or.inl ⟨h3p, h0p, h2p⟩)

end StatMech.FrontierA
