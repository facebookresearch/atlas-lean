/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import FormalizedTextbooks.FrenkelLepowskyMeurmanMonster.GeneratedAxisGlobalIdentWOddDistinct

/-! # The odd part of the tensor pairing in groups of source terms (r8f)

The odd short terms of the source representation `L` enter the tensor part of the pairing through
`oddLZ w fwd Y L`, one packed read of the target tensor per odd term.  For a listed short block it
is additive over groups of source terms (`oddLZ_ofList`, `oddSumL_append`), so that dense sources
can be evaluated group by group. -/

@[expose] public section
namespace FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
namespace GeneratedAxisGlobalIdent
set_option autoImplicit false

/-- The odd part of the tensor pairing over the odd terms of a term list. -/
def oddSumL (w : ℕ) (fwd : Bool) (Y : List SVec) (T : List (ℕ × ℤ)) : ℤ :=
  ((T.filter (fun p => decide (49128 ≤ p.1))).map (fun q => q.2 * oddLTerm w fwd Y q.1)).sum

/-- The odd part of the tensor pairing is additive over concatenation. -/
theorem oddSumL_append (w : ℕ) (fwd : Bool) (Y : List SVec) (A B : List (ℕ × ℤ)) :
    oddSumL w fwd Y (A ++ B) = oddSumL w fwd Y A + oddSumL w fwd Y B := by
  unfold oddSumL
  rw [List.filter_append, List.map_append, List.sum_append]

/-- The odd part of the tensor pairing of a source with a listed short block. -/
theorem oddLZ_ofList (w : ℕ) (fwd : Bool) (Y : List SVec) (M : MatRep) (T : List (ℕ × ℤ))
    (d : ℚ) (t : GeneratedAxisGlobalRationalTensor) :
    oddLZ w fwd Y ⟨M, ShortData.ofList T, d, t⟩ = oddSumL w fwd Y T := rfl

end GeneratedAxisGlobalIdent
end FormalizedTextbooks.FrenkelLepowskyMeurmanMonster
