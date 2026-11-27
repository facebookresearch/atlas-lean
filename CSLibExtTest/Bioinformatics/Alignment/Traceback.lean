/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import CSLibExt.Bioinformatics.Alignment.Traceback

/-!
# Needleman–Wunsch and Smith–Waterman traceback tests

Kernel-checked examples: empty inputs, a three-way tie, the zero stop, the case with no positive
local alignment, the positive-gap gap between `swTab` and `localScore`, `argmaxCell` on tables with
and without a `(0, 0)` entry, and an alignment that uses every move. Executed fixtures (`#guard`):
the compiled tracebacks on concrete alignments and on long skewed inputs, where one sequence has
at most one letter. There the table has a number of cells linear in the input length, each
traceback move makes a bounded number of scorer calls, score operations and array accesses, and the
scorer `s` below takes constant time on these small scores, so the runs take time linear in their
length. This is a property of these inputs, not a time bound for every scorer.

This file is not a `module`: the tables are built with `List.scanl`, whose definition a module
import does not expose, so `decide +kernel` could not evaluate the tracebacks there.
-/

namespace CSLibExtTest.Bioinformatics.Alignment.Traceback

open Cslib.Algorithms.Lean Cslib.Bioinformatics.Alignment.Traceback

/-- Match `2`, mismatch `-1`. -/
def s (a b : ℕ) : ℤ := if a = b then 2 else -1

example : nwTraceback s (-1) [1, 2, 3] [1, 3] =
    [(some 1, some 1), (some 2, none), (some 3, some 3)] := by
  decide +kernel

example : alignmentScore s (-1) (nwTraceback s (-1) [1, 2, 3] [1, 3]) = 3 := by decide +kernel

example : nwTraceback s (-1) [] [1, 3] = [(none, some 1), (none, some 3)] := by decide +kernel

example : nwTraceback s (-1) [1, 2] [] = [(some 1, none), (some 2, none)] := by decide +kernel

example : nwTraceback s (-1) ([] : List ℕ) [] = [] := by decide +kernel

example : swTraceback s (-1) [5, 1, 2, 3, 6] [7, 1, 3, 8] =
    { xStart := 1, xEnd := 4, yStart := 1, yEnd := 3,
      alignment := [(some 1, some 1), (some 2, none), (some 3, some 3)] } := by
  decide +kernel

/-- No positive local alignment: the empty alignment of two empty infixes. -/
example : swTraceback s (-1) [5, 6] [7, 8] =
    { xStart := 0, xEnd := 0, yStart := 0, yEnd := 0, alignment := [] } := by
  decide +kernel

/-- A positive gap: the traceback still attains `swTab = 3`, which is below the local optimum. -/
example : swTraceback s 1 [5, 6] [7, 8] =
    { xStart := 0, xEnd := 2, yStart := 1, yEnd := 2,
      alignment := [(some 5, none), (none, some 8), (some 6, none)] } := by
  decide +kernel

example : Cslib.Bioinformatics.Alignment.SmithWaterman.swTab s 1 [5, 6] [7, 8] = 3 := by
  decide +kernel

example : localScore s 1 [5, 6] [7, 8] = 4 := by decide +kernel

/-- `argmaxCell` returns a real entry even when row `0` is empty. The `(0, 0)` fallback is used
only when the table has no entry. -/
example : argmaxCell [[], [-1]] = (1, 0) := by decide +kernel

example : argmaxCell [[], [0]] = (1, 0) := by decide +kernel

example : argmaxCell [] = (0, 0) := by decide +kernel

example : argmaxCell [[], []] = (0, 0) := by decide +kernel

/-- Ties keep the first largest entry. -/
example : argmaxCell [[-2, -1], [-1]] = (0, 1) := by decide +kernel

/-! Predecessor ties, over any alphabet: one symbol per sequence, so cell `(1, 1)` is the only
interior cell and the scores alone decide which predecessors attain it. -/

/-- A three-way predecessor tie: with zero substitution and gap scores, the diagonal, up and left
predecessors of cell `(1, 1)` all give its value `0`, and the traceback takes the diagonal, a
single column. -/
example {α : Type} (a b : α) : nwTraceback (fun _ _ => 0) 0 [a] [b] = [(some a, some b)] := rfl

/-- Up before left: substitution score `-1` and gap score `0` leave the up and left predecessors
of cell `(1, 1)` tied, and the traceback steps up first. -/
example {α : Type} (a b : α) :
    nwTraceback (fun _ _ => -1) 0 [a] [b] = [(none, some b), (some a, none)] := rfl

/-- The same three-way tie in the local traceback, with substitution and gap score `1`: cell
`(1, 1)` is the largest, and the traceback takes the diagonal. -/
example {α : Type} (a b : α) :
    swTraceback (fun _ _ => 1) 1 [a] [b] =
      { xStart := 0, xEnd := 1, yStart := 0, yEnd := 1, alignment := [(some a, some b)] } := rfl

/-- Up before left in the local traceback: substitution score `0` and gap score `1`. -/
example {α : Type} (a b : α) :
    swTraceback (fun _ _ => 0) 1 [a] [b] =
      { xStart := 0, xEnd := 1, yStart := 1, yEnd := 1, alignment := [(some a, none)] } := rfl

/-! The workers' early returns: with fuel `0` they stop at once, the local worker even at the
nonzero interior cell `(1, 1)`, and with a letter missing they stop where they are. -/

example : swTraceAux s 1 #[#[0, 0], #[0, 1]] #[5] #[7] 0 1 1 [] = (1, 1, []) := by decide +kernel

example : nwTraceAux s (-1) #[#[0, -1], #[-1, 2]] #[1] #[1] 0 1 1 [] = [] := by decide +kernel

example : swTraceAux s (-1) #[#[0, 0], #[0, 2]] #[] #[1] 2 1 1 [] = (1, 1, []) := by
  decide +kernel

example : nwTraceAux s (-1) #[#[0, -1], #[-1, 2]] #[] #[1] 2 1 1 [] = [] := by decide +kernel

/-- Diagonal, up, diagonal, left, diagonal: an optimal alignment of score `4`. -/
example : nwTraceback s (-1) [1, 2, 3, 5] [1, 3, 4, 5] =
    [(some 1, some 1), (some 2, none), (some 3, some 3), (none, some 4), (some 5, some 5)] := by
  decide +kernel

#guard nwTraceback s (-1) [1, 2, 3, 5] [1, 3, 4, 5] ==
  [(some 1, some 1), (some 2, none), (some 3, some 3), (none, some 4), (some 5, some 5)]

-- The same alignment, read back locally between the mismatched ends.
#guard swTraceback s (-1) [9, 1, 2, 3, 5, 9] [8, 1, 3, 4, 5, 8] ==
  { xStart := 1, xEnd := 5, yStart := 1, yEnd := 5,
    alignment :=
      [(some 1, some 1), (some 2, none), (some 3, some 3), (none, some 4), (some 5, some 5)] }

-- An empty first sequence: `10⁶` steps along the top border.
#guard nwTraceback s (-1) [] (List.replicate 1000000 1) == List.replicate 1000000 (none, some 1)

-- An empty second sequence: `10⁵` steps along the left border.
#guard nwTraceback s (-1) (List.replicate 100000 2) [] == List.replicate 100000 (some 2, none)

-- A one-letter first sequence: one diagonal step, then `10⁵ - 1` steps along the top border.
#guard nwTraceback s (-1) [1] (List.replicate 100000 1) ==
  List.replicate 99999 (none, some 1) ++ [(some 1, some 1)]

-- A positive gap: the local traceback walks `10⁵ - 1` cells left along row `1`.
#guard swTraceback s 1 [5] (List.replicate 100000 7) ==
  { xStart := 0, xEnd := 1, yStart := 1, yEnd := 100000,
    alignment := (some 5, none) :: List.replicate 99999 (none, some 7) }

end CSLibExtTest.Bioinformatics.Alignment.Traceback
