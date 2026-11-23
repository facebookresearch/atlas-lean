/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Algorithms.Lean.StringMatching.KnuthMorrisPratt
import CSLibExt.Algorithms.Lean.StringMatching.Naive
meta import CSLibExt.Algorithms.Lean.StringMatching.KnuthMorrisPratt
meta import CSLibExt.Algorithms.Lean.StringMatching.Naive
meta import Plausible.Random

/-!
# KMP first-match runtime tests

Execute `kmpSearch` itself, not a theorem or a copied implementation. The
independent alignment-by-alignment oracle is `naiveMatches`, projected to its
first offset. Its membership and ordering theorems give the same `MatchAt`
semantics as `kmpSearch_eq_some_iff` and `kmpSearch_eq_none_iff`, including
`some 0` for an empty pattern. All symbols use Nat's lawful Boolean equality.

The frozen corpus has 16 literal answers, all 3,937 binary pattern/text pairs
of lengths at most 4/6, and 600 Plausible samples with seed 2026111901.
The samples have six equal strata: independent words, planted matches,
absent symbols, repeated overlaps, prefix near misses, and overlong patterns.
Generated pattern/text lengths are at most 17/24, with symbols in 0..3.
The printed bins measure input shapes, not internal branch coverage.
Finite agreement is not a theorem, a cost check, or a machine-time bound.

Replay from the repository root:
```
lake --wfail build CSLibExtTest.Algorithms.Lean.StringMatching.KnuthMorrisPrattRuntimeTests
lake env lean -DwarningAsError=true CSLibExtTest/Algorithms/Lean/StringMatching/KnuthMorrisPrattRuntimeTests.lean
```
-/

open Cslib.Algorithms.Lean.TimeM

private meta def checkCase
    (search : List Nat → List Nat → Option Nat)
    (pattern text : List Nat) : IO (List Nat) := do
  let offsets := (naiveMatches pattern text).ret
  let expected := offsets.head?
  let actual := search pattern text
  unless actual == expected do
    throw (IO.userError s!"first-match mismatch: pattern={pattern} text={text} \
      expected={repr expected} actual={repr actual}")
  return offsets

private meta def search (pattern text : List Nat) : Option Nat :=
  (kmpSearch pattern text).ret

private meta def literals : List (List Nat × List Nat × Option Nat) :=
  [([], [], some 0),
   ([], [0, 1, 2], some 0),
   ([0], [], none),
   ([0], [1], none),
   ([0], [0], some 0),
   ([0, 1, 2], [0, 1, 2], some 0),
   ([0, 1, 2], [0, 1], none),
   ([1, 2], [0, 0, 1, 2], some 2),
   ([0, 0, 0], [0, 0, 0, 0, 0], some 0),
   ([1, 2], [0, 1, 2, 1, 2], some 1),
   ([0, 1, 0], [0, 1, 0, 1, 0], some 0),
   ([0, 1, 0, 1, 0, 2, 0], [0, 1, 0, 1, 0, 1, 0, 2, 0], some 2),
   ([0, 0, 0, 0, 0, 1], [0, 0, 0, 0, 0, 0], none),
   ([0, 0, 1], [0, 0, 0, 0, 1], some 2),
   ([0, 1, 2], [1, 0, 1], none),
   ([257, 65537], [0, 257, 65537, 257, 65537], some 1)]

private meta def binaryWords : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 => [0, 1].flatMap fun x => (binaryWords n).map (x :: ·)

private meta def wordsThrough (n : Nat) : List (List Nat) :=
  (List.range (n + 1)).flatMap binaryWords

private meta def chooseUpTo (n : Nat) : Plausible.Rand Nat := do
  return (← Plausible.Random.randBound Nat 0 n (Nat.zero_le n)).val

private meta def randomWord (n : Nat) : Plausible.Rand (List Nat) :=
  (List.range n).mapM fun _ => chooseUpTo 2

private meta def sample (stratum : Nat) :
    Plausible.Rand (List Nat × List Nat) := do
  match stratum with
  | 0 =>
    let m ← chooseUpTo 12
    let n ← chooseUpTo 24
    return (← randomWord m, ← randomWord n)
  | 1 =>
    let m := (← chooseUpTo 7) + 1
    let before ← chooseUpTo 8
    let after ← chooseUpTo 8
    let p ← randomWord m
    let pre ← randomWord before
    let post ← randomWord after
    return (p, pre ++ p ++ post)
  | 2 =>
    let m := (← chooseUpTo 7) + 1
    let n ← chooseUpTo 24
    return ((← randomWord m) ++ [3], ← randomWord n)
  | 3 =>
    let x ← chooseUpTo 2
    let m := (← chooseUpTo 7) + 1
    let extra := (← chooseUpTo 7) + 1
    return (List.replicate m x, List.replicate (m + extra) x)
  | 4 =>
    let m := (← chooseUpTo 6) + 2
    let k := (← chooseUpTo 7) + 1
    return (List.replicate m 0 ++ [1], List.replicate (m + k) 0 ++ [1])
  | _ =>
    let n ← chooseUpTo 8
    let k ← chooseUpTo 8
    let t ← randomWord n
    return (← randomWord (n + 1 + k), t)

private meta def generatedInputs :
    Plausible.Rand (List (List (List Nat × List Nat))) :=
  (List.range 6).mapM fun stratum =>
    (List.range 100).mapM fun _ => sample stratum

private meta def shapeNames : List String :=
  ["emptyPattern", "emptyText", "absent", "overlength", "nonemptyAtZero",
   "later", "multiple", "overlapping", "repeatedPattern", "prefixNearMiss"]

private meta def shapes (pattern text offsets : List Nat) : List Bool :=
  [pattern.isEmpty,
   text.isEmpty,
   offsets.isEmpty,
   pattern.length > text.length,
   !pattern.isEmpty && offsets.head? == some 0,
   offsets.head?.any (· > 0),
   offsets.length > 1,
   offsets.any fun i => offsets.any fun j =>
     i < j && j < i + pattern.length,
   pattern.length > 1 && pattern.all (· == pattern.headD 0),
   pattern.length ≥ 3 && (List.range text.length).any fun i =>
     i < offsets.head?.getD (text.length + 1) &&
       (pattern.take (pattern.length - 1)).isPrefixOf (text.drop i) &&
       !pattern.isPrefixOf (text.drop i)]

private meta def runTests : IO Unit := do
  let patterns := wordsThrough 4
  let texts := wordsThrough 6
  let exhaustive := patterns.flatMap fun p => texts.map (p, ·)
  let strata := (generatedInputs.run ⟨mkStdGen 2026111901⟩).1
  let generated := strata.flatten
  unless patterns.length == 31 && texts.length == 127 &&
      exhaustive.length == 3937 && literals.length == 16 &&
      strata.length == 6 && strata.all (·.length == 100) &&
      generated.length == 600 do
    throw (IO.userError "corpus cardinality")
  unless generated.all (fun (p, t) => p.length ≤ 17 && t.length ≤ 24 &&
      (p ++ t).all (· ≤ 3)) do
    throw (IO.userError "generated bounds")
  let symbols := generated.flatMap fun (p, t) => p ++ t
  let symbolCounts := (List.range 4).map symbols.count
  unless symbolCounts.all (· > 0) do
    throw (IO.userError "generated alphabet coverage")
  let mut counts := List.replicate shapeNames.length 0
  let mut checks := 0
  for (p, t, expected) in literals do
    let offsets ← checkCase search p t
    unless offsets.head? == expected do
      throw (IO.userError s!"literal oracle mismatch: pattern={p} text={t}")
    counts := counts.zipWith (fun n b => n + if b then 1 else 0)
      (shapes p t offsets)
    checks := checks + 1
  for (p, t) in exhaustive ++ generated do
    let offsets ← checkCase search p t
    counts := counts.zipWith (fun n b => n + if b then 1 else 0)
      (shapes p t offsets)
    checks := checks + 1
  unless checks == 4553 && counts.length == shapeNames.length &&
      counts.all (· > 0) do
    throw (IO.userError s!"input-shape coverage: checks={checks} bins={counts}")
  IO.println s!"KMP first-match: literal={literals.length} \
    exhaustive={exhaustive.length} generated={generated.length} checks={checks}"
  IO.println s!"seed=2026111901 strata={strata.map List.length} \
    sampleHash={hash generated} retries=0 discards=0"
  IO.println s!"generated symbol counts={symbolCounts}"
  IO.println s!"input shapes={repr (shapeNames.zip counts)}"

#eval runTests
