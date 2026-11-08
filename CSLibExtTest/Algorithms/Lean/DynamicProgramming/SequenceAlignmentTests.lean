/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment
public meta import CSLibExt.Algorithms.Lean.DynamicProgramming.SequenceAlignment

/-!
# Sequence alignment tests

Executed fixtures: on all pairs of `Bool` sequences of length at most 3, with
match `2`, mismatch `-1`, gap `-1`, the terminal Smith–Waterman cell equals the maximum
Needleman–Wunsch score over suffix pairs, the local score equals the Smith–Waterman
score (the maximum cell over prefixes), and the Needleman–Wunsch score equals the
maximum alignment score over all enumerated alignments. Closed checks
instantiate the theorems and the axiom audit.
-/

namespace Cslib.Algorithms.Lean

/-- Match `2`, mismatch `-1` scoring, used by the tests below. -/
def testScore : Bool → Bool → ℤ := fun a b => if a = b then 2 else -1

#eval do
  let allLists : List (List Bool) :=
    [[], [true], [false], [true, true], [true, false], [false, true], [false, false],
     [true, true, true], [true, true, false], [true, false, true], [true, false, false],
     [false, true, true], [false, true, false], [false, false, true], [false, false, false]]
  for xs in allLists do
    for ys in allLists do
      unless swCellScore testScore (-1) xs ys == suffixMax testScore (-1) xs ys do
        throw (IO.userError
          s!"swCellScore {swCellScore testScore (-1) xs ys} ≠ suffixMax {suffixMax testScore (-1) xs ys} at {xs} {ys}")
      unless localScore testScore (-1) xs ys == swScore testScore (-1) xs ys do
        throw (IO.userError
          s!"localScore {localScore testScore (-1) xs ys} ≠ prefixMax {swScore testScore (-1) xs ys} at {xs} {ys}")
      let scores := (alignments xs ys).map (alignmentScore testScore (-1))
      unless scores.all (fun s => decide (s ≤ nwScore testScore (-1) xs ys))
          && scores.contains (nwScore testScore (-1) xs ys) do
        throw (IO.userError s!"NW score is not the max alignment score at {xs} {ys}")
  IO.println "225 Bool pairs: SW cell = suffix max, local = SW score, NW = max alignment score"

/-! Closed checks -/

example : nwScore testScore (-1) [true, false] [true, false] = 4 := by decide

example : swCellScore testScore (-1) [true, false] [false] = 2 := by decide

-- Regression: the terminal cell is `1` here while the optimal local score is `2`.
example : swCellScore testScore (-1) [true, false] [true, true] = 1 := by decide

-- Regression: for positive gaps the cell need not equal the optimal local score,
-- so the suffix-max / local-score characterizations genuinely need `gap ≤ 0`.
example : swCellScore (fun _ _ => (-100 : ℤ)) 1 [true] [true] = 1 := by decide

example : localScore (fun _ _ => (-100 : ℤ)) 1 [true] [true] = 2 := by decide

example : swScore testScore (-1) [true, false] [true, true] = 2 := by decide

set_option maxRecDepth 8192 in
example : localScore testScore (-1) [true, false] [true, true] = 2 := by decide

set_option maxRecDepth 8192 in
example : localScore testScore (-1) [true, false, true] [false, true] = 4 := by decide

-- The recurrence API needs no `DecidableEq`: functions `ℕ → ℕ` have no
-- `DecidableEq` instance, yet `swCellScore_eq` still applies to them.
example (σ : (ℕ → ℕ) → (ℕ → ℕ) → ℤ) (gap : ℤ) (xs ys : List (ℕ → ℕ)) (a b : ℕ → ℕ) :
    swCellScore σ gap (xs ++ [a]) (ys ++ [b]) =
      max 0 (max (max (swCellScore σ gap xs ys + σ a b)
        (swCellScore σ gap xs (ys ++ [b]) + gap))
        (swCellScore σ gap (xs ++ [a]) ys + gap)) :=
  swCellScore_eq σ gap xs ys a b

-- The characterization API also needs no `DecidableEq`: the suffix maximum, local
-- score, and Smith–Waterman score are list maxima over list candidate collections.
example (σ : (ℕ → ℕ) → (ℕ → ℕ) → ℤ) (gap : ℤ) (xs ys : List (ℕ → ℕ))
    (hgap : gap ≤ 0) :
    swCellScore σ gap xs ys = suffixMax σ gap xs ys ∧
      localScore σ gap xs ys = swScore σ gap xs ys :=
  ⟨swCellScore_eq_suffixMax σ gap hgap xs ys, localScore_eq_swScore σ gap hgap xs ys⟩

example (hgap : (-1 : ℤ) ≤ 0) (xs ys : List Bool) :
    swCellScore testScore (-1) xs ys = suffixMax testScore (-1) xs ys :=
  swCellScore_eq_suffixMax testScore (-1) hgap xs ys

example (hgap : (-1 : ℤ) ≤ 0) (xs ys : List Bool) :
    localScore testScore (-1) xs ys = swScore testScore (-1) xs ys :=
  localScore_eq_swScore testScore (-1) hgap xs ys

#print axioms swCellScore_eq_suffixMax
#print axioms localScore_eq_swScore
#print axioms nwScore_snoc
#print axioms exists_alignmentScore_eq_nwScore

end Cslib.Algorithms.Lean
