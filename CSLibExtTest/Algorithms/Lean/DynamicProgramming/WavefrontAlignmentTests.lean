/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.WavefrontAlignment
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.WavefrontAlignment

/-!
# Wavefront alignment tests

Unit costs (`x = g = 1`): `kitten` to `sitting` is first reached at score `3`, and not at `2`;
the empty source against `abc` at score `3`. Mismatch `3`, gap `1`: `kitten`/`sitting` costs `5`
(each substitution is cheaper as a deletion plus an insertion), and `ab`/`ba` costs `2`, which
is `-nwScore`. Boundary: two empty sequences are aligned at score `0`; diagonals outside
`[-|xs|, |ys|]` are unreachable. Non-vacuity: a concrete penalty structure; the theorems
instantiated. Axiom audit follows.
-/

namespace Cslib.Algorithms.Lean.Wavefront

/-- Unit costs. -/
def unit : LinearPenalties := ⟨1, 1, Nat.one_pos, Nat.one_pos⟩

/-- Mismatch `3`, gap `1`. -/
def mis3 : LinearPenalties := ⟨3, 1, by norm_num, Nat.one_pos⟩

/-- Whether the wavefront of score `s` reaches the end cell. -/
def reaches (P : LinearPenalties) (xs ys : List Char) (s : ℕ) : Bool :=
  wavefront P xs ys s ((ys.length : ℤ) - xs.length) == some (ys.length : ℤ)

#guard reaches unit "kitten".toList "sitting".toList 3
#guard !reaches unit "kitten".toList "sitting".toList 2
#guard !reaches unit "kitten".toList "sitting".toList 1
#guard reaches unit [] "abc".toList 3
#guard !reaches unit [] "abc".toList 2
#guard reaches mis3 "kitten".toList "sitting".toList 5
#guard !reaches mis3 "kitten".toList "sitting".toList 4
#guard reaches mis3 "ab".toList "ba".toList 2
#guard !reaches mis3 "ab".toList "ba".toList 1
#guard nwScore mis3.score (-(mis3.gap : ℤ)) "ab".toList "ba".toList = -2
#guard reaches unit [] [] 0
#guard wavefront unit "ab".toList "abc".toList 2 4 = none
#guard wavefront unit "ab".toList "abc".toList 2 (-3) = none
#guard wavefront unit "acgt".toList "acgt".toList 0 0 = some 4

example (s : ℕ) :
    (∃ s' ≤ s, wavefront unit "ab".toList "ba".toList s'
        (("ba".toList.length : ℤ) - "ab".toList.length) = some "ba".toList.length) ↔
      -nwScore unit.score (-(unit.gap : ℤ)) "ab".toList "ba".toList ≤ s :=
  exists_wavefront_end_iff_nwScore unit _ _ s

#print axioms wavefront_sound
#print axioms wavefront_complete
#print axioms exists_wavefront_end_iff
#print axioms exists_wavefront_end_iff_nwScore

end Cslib.Algorithms.Lean.Wavefront
