/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Breakpoint 2-approximation for unsigned sorting by reversals

For an unsigned permutation `π` of `1..n` (as a list with each value exactly
once), framed by `0` and `n+1`, a breakpoint is an adjacent framed pair that
is not consecutive. A strip is a maximal breakpoint-free segment; a
decreasing strip steps down by one. The greedy algorithm repeatedly applies
a reversal removing the most breakpoints (preferring, among single-breakpoint
removals, one that leaves a decreasing strip). Every greedy run sorts `π`
within `φ(π)` reversals (`φ` the breakpoint count); since one reversal
removes at most two breakpoints, `OPT(π) ≥ φ(π)/2`, so greedy is a
2-approximation. Time (`O(n^2)`) and space (`O(n)`) readings need cost
models and are context here.

Overlap (partial base): `CSLibExt/Bioinformatics/Rearrangement/SortingByReversals.lean`
proves the breakpoint lower bound `b ≤ 2d` and sortability; the greedy
procedure, its `φ` upper bound, and the 2-approximation are new.

Sources: J. Kececioglu and D. Sankoff, "Exact and approximation algorithms
for sorting by reversals, with application to genome rearrangement",
Algorithmica 13(1-2):180-210, 1995, doi:10.1007/BF01188586, Theorem 1 and
Corollary 1.
-/
module

public import Batteries.Util.ProofWanted
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.List.Basic

@[expose] public section

namespace WantedExt.Biology.ComputationalBiology.GreedyReversalWanted

open Classical

/-- Valid unsigned permutations of `1..n`. -/
def IsPerm (n : ℕ) (π : List ℕ) : Prop :=
  π.length = n ∧ ∀ v, 1 ≤ v → v ≤ n → v ∈ π

/-- The sorted identity n `1..n`. -/
def identity (n : ℕ) : List ℕ :=
  (List.range n).map (· + 1)

/-- Framing with sentinels `0` and `n+1`. -/
def framed (n : ℕ) (π : List ℕ) : List ℕ :=
  0 :: π ++ [n + 1]

/-- Consecutive values (either direction). -/
def Consecutive (x y : ℕ) : Prop :=
  x + 1 = y ∨ y + 1 = x

/-- Breakpoint count of the framed permutation. -/
noncomputable def breakpoints (n : ℕ) (π : List ℕ) : ℕ :=
  ((List.range (framed n π).length).filter fun i =>
    ∃ x y, (framed n π).getD i 0 = x ∧ (framed n π).getD (i + 1) 0 = y ∧
      ¬ Consecutive x y).length

/-- Core reversal on framed lists: reverse positions `[i+1, j]`. -/
def applyReversalCore (F : List ℕ) (r : ℕ × ℕ) : List ℕ :=
  F.take (r.1 + 1) ++ ((F.drop (r.1 + 1)).take (r.2 - r.1)).reverse ++
    F.drop (r.2 + 1)

/-- Unframe: drop both sentinels. -/
def unframe (F : List ℕ) : List ℕ :=
  F.drop 1 |>.dropLast

/-- Run result: fold reversals over the framed list, then unframe. -/
def runResult (n : ℕ) (π : List ℕ) (seq : List (ℕ × ℕ)) : List ℕ :=
  unframe (seq.foldl applyReversalCore (framed n π))

/-- Breakpoints removed (net) by a reversal, over `ℤ`. -/
noncomputable def removed (n : ℕ) (π : List ℕ) (r : ℕ × ℕ) : ℤ :=
  (breakpoints n π : ℤ) - breakpoints n (unframe (applyReversalCore (framed n π) r))

/-- Breakpoint-free segments. -/
def StripBreaks (S : List ℕ) : Prop :=
  ∀ i : ℕ, i + 1 < S.length →
    Consecutive (S.getD i 0) (S.getD (i + 1) 0)

/-- Strips: maximal breakpoint-free sublists of the framed permutation. -/
def IsStrip (n : ℕ) (π S : List ℕ) : Prop :=
  S.Sublist (framed n π) ∧ StripBreaks S ∧
    ∀ T : List ℕ, S.Sublist T → T.Sublist (framed n π) → StripBreaks T →
      T.length ≤ S.length

/-- Decreasing strips step down by one (singletons count, except the two
framing elements, which are never decreasing). -/
def IsDecreasing (S : List ℕ) : Prop :=
  ∀ i : ℕ, i + 1 < S.length → S.getD i 0 = S.getD (i + 1) 0 + 1

/-- Greedy runs: chains of reversals from `π`. -/
inductive GreedyRun (n : ℕ) : List ℕ → List (ℕ × ℕ) → Prop where
  | nil (π) : GreedyRun n π []
  | cons (π π' : List ℕ) (r : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
      π' = unframe (applyReversalCore (framed n π) r) →
        GreedyRun n π' rest → GreedyRun n π (r :: rest)

/-- Optimal reversal count, characterized by `hopt_le`/`hopt_att` below. -/
noncomputable def optCount (n : ℕ) (π : List ℕ)
    (h : ∃ seq : List (ℕ × ℕ), runResult n π seq = identity n) : ℕ :=
  Nat.find (p := fun k => ∃ seq : List (ℕ × ℕ),
    runResult n π seq = identity n ∧ seq.length = k)
    (by obtain ⟨s, hs⟩ := h; exact ⟨s.length, s, hs, rfl⟩)

/-- **Greedy breakpoint algorithm sorts within φ(π)** (Kececioglu-Sankoff
1995, Theorem 1): hypotheses are a valid permutation (`hπ`), a greedy run
(`hrun`), maximal removal at each step (`hgreedy`), the decreasing-strip
tie-break among single removals (`htie`: when some removal-1 step leaves a
decreasing strip, the chosen step does), and at most two breakpoints removed
per reversal (`hmax2`). Conclusions: the run ends sorted with at most
`φ(π)` reversals.

Source: Kececioglu-Sankoff (1995), Theorem 1. -/
theorem_wanted greedy_sorts (n : ℕ) (π : List ℕ) (hπ : IsPerm n π)
    (seq : List (ℕ × ℕ))
    (hrun : GreedyRun n π seq)
    (hgreedy : ∀ A : List ℕ, ∀ r : ℕ × ℕ, ∀ rest : List (ℕ × ℕ),
      GreedyRun n A (r :: rest) →
        ∀ r' : ℕ × ℕ, removed n A r' ≤ removed n A r)
    (htie : ∀ A : List ℕ, ∀ r : ℕ × ℕ, ∀ rest : List (ℕ × ℕ),
      GreedyRun n A (r :: rest) → removed n A r = 1 →
      (∃ r' : ℕ × ℕ, removed n A r' = 1 ∧ ∃ S : List ℕ,
        IsStrip n (unframe (applyReversalCore (framed n A) r')) S ∧
          IsDecreasing S) →
      ∃ S : List ℕ,
        IsStrip n (unframe (applyReversalCore (framed n A) r)) S ∧
          IsDecreasing S)
    (hmax2 : ∀ A : List ℕ, ∀ r : ℕ × ℕ, removed n A r ≤ 2) :
    runResult n π seq = identity n ∧ seq.length ≤ breakpoints n π

/-- **Greedy is a 2-approximation** (Kececioglu-Sankoff 1995, Corollary 1):
same hypotheses as `greedy_sorts`, plus the optimum characterization
(`hopt_le`, `hopt_att`). Conclusion: run length `≤ 2 * OPT(π)`.

Source: Kececioglu-Sankoff (1995), Corollary 1. -/
theorem_wanted greedy_two_approx (n : ℕ) (π : List ℕ) (hπ : IsPerm n π)
    (seq : List (ℕ × ℕ))
    (hrun : GreedyRun n π seq)
    (hgreedy : ∀ A : List ℕ, ∀ r : ℕ × ℕ, ∀ rest : List (ℕ × ℕ),
      GreedyRun n A (r :: rest) →
        ∀ r' : ℕ × ℕ, removed n A r' ≤ removed n A r)
    (htie : ∀ A : List ℕ, ∀ r : ℕ × ℕ, ∀ rest : List (ℕ × ℕ),
      GreedyRun n A (r :: rest) → removed n A r = 1 →
      (∃ r' : ℕ × ℕ, removed n A r' = 1 ∧ ∃ S : List ℕ,
        IsStrip n (unframe (applyReversalCore (framed n A) r')) S ∧
          IsDecreasing S) →
      ∃ S : List ℕ,
        IsStrip n (unframe (applyReversalCore (framed n A) r)) S ∧
          IsDecreasing S)
    (hmax2 : ∀ A : List ℕ, ∀ r : ℕ × ℕ, removed n A r ≤ 2)
    (hex : ∃ s2 : List (ℕ × ℕ), runResult n π s2 = identity n)
    (hopt_le : ∀ s2 : List (ℕ × ℕ), runResult n π s2 = identity n →
      optCount n π hex ≤ s2.length)
    (hopt_att : ∃ s2 : List (ℕ × ℕ), runResult n π s2 = identity n ∧
      optCount n π hex = s2.length) :
    seq.length ≤ 2 * optCount n π hex

end WantedExt.Biology.ComputationalBiology.GreedyReversalWanted
