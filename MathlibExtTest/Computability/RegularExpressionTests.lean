/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

meta import Mathlib.Computability.RegularExpressions

/-! Direct whole-word `rmatch` tests. The independent predicates inspect words,
not `matches'` membership: its decidability instance calls `rmatch` itself. -/

namespace RegularExpressionTests

open RegularExpression

private meta def checkMatch (matchWord : RegularExpression Bool → List Bool → Bool)
    (name : String) (expression : RegularExpression Bool) (oracle : List Bool → Bool)
    (word : List Bool) : IO Unit := do
  let actual := matchWord expression word
  let expected := oracle word
  unless actual == expected do
    throw (IO.userError s!"regex {name} word={word} expected={expected} actual={actual}")

private meta def expressions :
    List (String × RegularExpression Bool × (List Bool → Bool)) :=
  [("zero", zero, fun _ => false),
   ("epsilon", epsilon, List.isEmpty),
   ("true", char true, fun w => w == [true]),
   ("either", char true + char false, fun w => w.length == 1),
   ("ordered", char true * char false, fun w => w == [true, false]),
   ("nullable", (epsilon + char true) * char false,
     fun w => w == [false] || w == [true, false]),
   ("allTrue", star (char true), fun w => w.all id),
   ("endsTrue", star (char true + char false) * char true,
     fun w => w.getLast? == some true)]

private meta def boolWords : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolWords n).flatMap fun w => [false :: w, true :: w]

private meta def generatedWords : Plausible.Rand (List (List Bool)) :=
  (List.range 1000).mapM fun _ => do
    let n ← Plausible.Random.randBound Nat 0 12 (by decide)
    (List.range n.val).mapM fun _ => Plausible.Random.rand Bool

private meta def runMatchTests : IO Unit := do
  let exhaustive := (List.range 9).flatMap boolWords
  let generated := (generatedWords.run ⟨mkStdGen 2026110403⟩).1
  let fixed := [[], [true], [false], [true, false], [false, true], [true, true],
    [false, false], [true, false, true], List.replicate 12 true,
    List.replicate 12 false, List.replicate 11 false ++ [true]]
  let lengths := (List.range 13).map fun n => (generated.filter (·.length == n)).length
  unless expressions.length == 8 && exhaustive.length == 511 &&
      exhaustive.eraseDups.length == 511 &&
      (List.range 9).all (fun n => (exhaustive.filter (·.length == n)).length == 2^n) &&
      generated.length == 1000 && lengths.all (· > 0) do
    throw (IO.userError "regex corpus coverage")
  for (kind, words) in [("fixed", fixed), ("exhaustive", exhaustive),
      ("generated", generated)] do
    for (name, expression, oracle) in expressions do
      let mut accepted := 0
      for w in words do
        unless w.length ≤ 12 do throw (IO.userError "regex word bound")
        checkMatch rmatch name expression oracle w
        if oracle w then accepted := accepted + 1
      unless (name == "zero" || accepted > 0) && accepted < words.length do
        throw (IO.userError s!"regex {name} {kind} missing branch")
      IO.println s!"S2 regex {name} {kind} checks={words.length} accepted={accepted}"
  IO.println s!"S2 regex seed=2026110403 sharedDraws={generated.length} retries=0 discards=0"
  IO.println s!"S2 regex generated lengths={lengths} trueBits={generated.flatten.count true}"

#eval runMatchTests

-- Separate proof-interface evidence; this is never the runtime oracle.
example (expression : RegularExpression Bool) (word : List Bool) :
    expression.rmatch word = true ↔ word ∈ expression.matches' :=
  expression.rmatch_iff_matches' word

end RegularExpressionTests
