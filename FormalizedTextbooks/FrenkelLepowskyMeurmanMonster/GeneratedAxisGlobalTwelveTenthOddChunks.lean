/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentPairOddZ
public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentOctadFastDense

/-! # Odd pairing parts of dense vectors in chunks

For dense short blocks (tens of thousands of odd terms) the integer odd parts `oddWZ` / `oddLZ`
(worker gident2) exceed the kernel memory budget in one check: every field read of a packed
column is a fresh big number.  Here the odd part of a vector whose short block is
`ShortData.ofList` of a concatenation of packed chunk lists is split into the sum of the parts
of the chunk groups, each evaluated in its own kernel check. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- `oddWZ` over the odd terms of a raw term list. -/
def oddWZT (w : ℕ) (fwd : Bool) (X : List SVec) (T : List (ℕ × ℤ)) : ℤ :=
  ((T.filter (fun p => decide (49128 ≤ p.1))).map (fun q => q.2 * oddWTerm w fwd X q.1)).sum

/-- `oddLZ` over the odd terms of a raw term list. -/
def oddLZT (w : ℕ) (fwd : Bool) (Y : List SVec) (T : List (ℕ × ℤ)) : ℤ :=
  ((T.filter (fun p => decide (49128 ≤ p.1))).map (fun q => q.2 * oddLTerm w fwd Y q.1)).sum

theorem oddWZT_append (w : ℕ) (fwd : Bool) (X : List SVec) (A B : List (ℕ × ℤ)) :
    oddWZT w fwd X (A ++ B) = oddWZT w fwd X A + oddWZT w fwd X B := by
  simp only [oddWZT, List.filter_append, List.map_append, List.sum_append]

theorem oddLZT_append (w : ℕ) (fwd : Bool) (Y : List SVec) (A B : List (ℕ × ℤ)) :
    oddLZT w fwd Y (A ++ B) = oddLZT w fwd Y A + oddLZT w fwd Y B := by
  simp only [oddLZT, List.filter_append, List.map_append, List.sum_append]

/-- The odd part against the triality image of `L`, from the raw term list of `W`. -/
theorem oddWZ_ofList (w : ℕ) (fwd : Bool) (X : List SVec) (W : IdentVec) (T : List (ℕ × ℤ))
    (hW : W.sh = ShortData.ofList T) : oddWZ w fwd X W = oddWZT w fwd X T := by
  unfold oddWZ oddWZT
  rw [hW]
  rfl

/-- The odd tensor part of `L`, from the raw term list of `L`. -/
theorem oddLZ_ofList (w : ℕ) (fwd : Bool) (Y : List SVec) (L : IdentVec) (T : List (ℕ × ℤ))
    (hL : L.sh = ShortData.ofList T) : oddLZ w fwd Y L = oddLZT w fwd Y T := by
  unfold oddLZ oddLZT
  rw [hL]
  rfl

/-- The terms of concatenated chunk lists. -/
theorem octChunkTerms_append (A B : List (ℕ × ℕ × ℕ)) :
    OctadDense.octChunkTerms (A ++ B) =
      OctadDense.octChunkTerms A ++ OctadDense.octChunkTerms B := by
  induction A with
  | nil => rfl
  | cons c cs ih => rw [List.cons_append, OctadDense.octChunkTerms, OctadDense.octChunkTerms, ih,
      List.append_assoc]

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
