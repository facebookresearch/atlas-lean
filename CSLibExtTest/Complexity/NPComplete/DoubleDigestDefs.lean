/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.DoubleDigestDefs

namespace MetaMathlibExt.Complexity.NPComplete.DoubleDigest

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : DoubleDigestInstance) :
    doubleDigestDec (bitEncode i) = true ↔ WellFormed i ∧ DoubleDigestFeasible i := by
  simp [doubleDigestDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : doubleDigestDec [true] = false := by
  have h : bitDecode (α := DoubleDigestInstance) [true] = none := rfl
  simp [doubleDigestDec, h]

/-- The orderings of a two-element list `[p, q]` with `p ≠ q`. -/
private theorem perm_pair {a : List ℕ} {p q : ℕ} (hpq : p ≠ q) (h : a.Perm [p, q]) :
    a = [p, q] ∨ a = [q, p] := by
  match a, h.length_eq with
  | [x, y], _ =>
    have hx : x ∈ [p, q] := h.subset (by simp)
    have hy : y ∈ [p, q] := h.subset (by simp)
    have hc := (List.perm_iff_count.1 h) p
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · simp [hpq] at hc
    · exact Or.inl rfl
    · exact Or.inr rfl
    · simp [hpq, Ne.symm hpq] at hc

/-- Enzyme 1 cuts a length-3 strand into `1, 2` (cut at `1`), enzyme 2 into `2, 1` (cut at
`2`); both enzymes together give `1, 1, 1`. -/
example : doubleDigestDec (bitEncode (([1, 2], [1, 2], [1, 1, 1]) : DoubleDigestInstance)) =
    true := by
  refine (accepts_encoding _).2 ⟨by unfold WellFormed; decide, [1, 2], [2, 1], by decide,
    by decide, by simp [cutPoints], ?_⟩
  simp [cutPoints, fragments, List.dedup_cons_of_mem, List.dedup_cons_of_notMem]

/-- Fragments `1, 2` for enzyme 1 and `3` for enzyme 2 merge to the cut points of `1, 2` or
`2, 1`, never to three fragments of length `1`. -/
example : doubleDigestDec (bitEncode (([1, 2], [3], [1, 1, 1]) : DoubleDigestInstance)) =
    false := by
  cases h : doubleDigestDec (bitEncode (([1, 2], [3], [1, 1, 1]) : DoubleDigestInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, a, b, ha, hb, -, hc⟩ := (accepts_encoding _).1 h
    obtain rfl := List.perm_singleton.1 hb
    rcases perm_pair (by decide) ha with rfl | rfl
    · simp [cutPoints, fragments, List.dedup_cons_of_mem, List.dedup_cons_of_notMem] at hc
    · simp [cutPoints, fragments, List.dedup_cons_of_mem, List.dedup_cons_of_notMem] at hc
      exact absurd hc (by decide)

/-- Two enzymes that both cut at `1` violate the disjointness of internal cut points. -/
example : doubleDigestDec (bitEncode (([1, 1], [1, 1], [1, 1]) : DoubleDigestInstance)) =
    false := by
  cases h : doubleDigestDec (bitEncode (([1, 1], [1, 1], [1, 1]) : DoubleDigestInstance)) with
  | false => rfl
  | true =>
    obtain ⟨-, a, b, ha, hb, hd, -⟩ := (accepts_encoding _).1 h
    have h₁ : a = [1, 1] := List.eq_replicate_iff.2 ⟨ha.length_eq, fun x hx => by
      simpa using ha.subset hx⟩ |>.trans rfl
    have h₂ : b = [1, 1] := List.eq_replicate_iff.2 ⟨hb.length_eq, fun x hx => by
      simpa using hb.subset hx⟩ |>.trans rfl
    subst h₁ h₂
    exact (hd (a := 1) (by simp [cutPoints]) (by simp [cutPoints])).elim

end MetaMathlibExt.Complexity.NPComplete.DoubleDigest
