/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Computability.Decidability.RegularExpression
meta import CSLibExt.Computability.Decidability.RegularExpression
meta import Plausible.Random

/-!
# Runtime witnesses for encoded-regex membership

Exercise `EncodedRegex.memB`, the CFG-based decider, against the independent derivative
matcher `RegularExpression.rmatch`. The shared specification is language membership via
`EncodedRegex.memB_iff` and `RegularExpression.rmatch_iff_matches'`.

The concrete alphabet is `Bool`. Invalid child references denote zero expressions, not
parse errors; in particular, the star of an invalid child accepts the empty word. Empty
encodings denote zero, and the last node is the root. These checks are finite runtime
regressions, not new proofs, a complexity bound, or a test of POSIX/substring matching.
-/

namespace Cslib.Language.EncodedRegex.RuntimeTests

private meta def fixed : List (String × EncodedRegex Bool) := [
  ("empty", ⟨[]⟩),
  ("zero", ⟨[.zero]⟩),
  ("epsilon", ⟨[.epsilon]⟩),
  ("false", ⟨[.char false]⟩),
  ("true", ⟨[.char true]⟩),
  ("union", ⟨[.char false, .char true, .plus 0 1]⟩),
  ("concat01", ⟨[.char false, .char true, .comp 0 1]⟩),
  ("concat10", ⟨[.char false, .char true, .comp 1 0]⟩),
  ("star", ⟨[.char false, .star 0]⟩),
  ("duplicate-epsilon", ⟨[.epsilon, .plus 0 0]⟩),
  ("nested-star", ⟨[.char false, .star 0, .star 1]⟩),
  ("ends-true", ⟨[.char true, .char false, .plus 0 1, .star 2, .char true, .comp 3 4]⟩),
  ("self-plus-right", ⟨[.char true, .plus 0 1]⟩),
  ("forward-plus-left", ⟨[.char false, .plus 2 0]⟩),
  ("forward-comp", ⟨[.char false, .comp 0 2]⟩),
  ("self-star", ⟨[.star 0]⟩),
  ("last-zero", ⟨[.char false, .zero]⟩),
  ("unused-invalid-node", ⟨[.char true, .plus 0 99, .char false]⟩)]

private meta def wordsUpTo : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => [] :: (wordsUpTo n).flatMap (fun w => [false :: w, true :: w])

-- The adapter parameter lets an external mutation harness reuse this exact checker.
private meta def checkMembership (accept : EncodedRegex Bool → List Bool → Bool)
    (e : EncodedRegex Bool) (w : List Bool) : Except String Bool := do
  let expected := e.toRegex.rmatch w
  let actual := accept e w
  unless actual == expected do
    throw s!"membership word={w} expected={expected} actual={actual}"
  return actual

private meta def generated : Plausible.Rand (List (EncodedRegex Bool × List Bool)) :=
  (List.range 64).mapM fun sample => do
    -- Stratify root constructors (6 = empty encoding), node counts, and word lengths.
    let root := sample % 7
    let n := if root == 6 then 0 else sample / 7 % 5 + 1
    let nodes ← (List.range n).mapM fun k => do
      let tag ← Plausible.Random.randBound Nat 0 5 (by decide)
      let letter ← Plausible.Random.randBound Nat 0 1 (by decide)
      let i ← Plausible.Random.randBound Nat 0 (k + 1) (Nat.zero_le _)
      let j ← Plausible.Random.randBound Nat 0 (k + 1) (Nat.zero_le _)
      return match (if k + 1 == n then root else tag.val) with
        | 0 => .zero
        | 1 => .epsilon
        | 2 => .char (letter.val == 1)
        | 3 => .plus i.val j.val
        | 4 => .comp i.val j.val
        | _ => .star i.val
    let word ← (List.range (sample % 5)).mapM fun _ => do
      return (← Plausible.Random.randBound Nat 0 1 (by decide)).val == 1
    return (⟨nodes⟩, word)

private meta def rootTag (e : EncodedRegex Bool) : Nat :=
  match e.nodes.getLast? with
  | none => 6
  | some .zero => 0
  | some .epsilon => 1
  | some (.char _) => 2
  | some (.plus _ _) => 3
  | some (.comp _ _) => 4
  | some (.star _) => 5

private meta def checkLiteral (e : EncodedRegex Bool) (w : List Bool)
    (expected : Bool) : IO Unit := do
  unless e.memB w == expected do
    throw (IO.userError s!"literal boundary word={w} expected={expected}")

private meta def runMembershipTests : IO Unit := do
  let inputs := (generated.run ⟨mkStdGen 2026111801⟩).1
  let roots := (List.range 7).map fun t => (inputs.filter (fun p => rootTag p.1 == t)).length
  let lengths := (List.range 5).map fun n => (inputs.filter (fun p => p.2.length == n)).length
  let sizes := (List.range 6).map fun n => (inputs.filter (fun p => p.1.nodes.length == n)).length
  let letters := [false, true].map fun a => (inputs.flatMap Prod.snd).count a
  unless inputs.length == 64 && roots.all (· > 0) && lengths.all (· > 0) &&
      sizes.all (· > 0) && letters.all (· > 0) do
    throw (IO.userError "encoded-regex generator coverage")
  for (e, w) in inputs do
    unless e.nodes.length ≤ 5 && w.length ≤ 4 do
      throw (IO.userError "encoded-regex generator bounds")
  let words := wordsUpTo 3
  unless fixed.length == 18 && words.length == 15 && words.eraseDups.length == 15 &&
      words.all (fun w => w.length ≤ 3) do
    throw (IO.userError "encoded-regex exhaustive corpus")
  let cases := fixed.flatMap (fun (name, e) => words.map fun w => (name, e, w)) ++
    inputs.zipIdx.map (fun ((e, w), i) => (s!"generated-{i}", e, w))
  unless cases.length == 334 do
    throw (IO.userError "encoded-regex total comparison count")
  let mut accepted := 0
  for (name, e, w) in cases do
    match checkMembership memB e w with
    | .ok result => if result then accepted := accepted + 1
    | .error error => throw (IO.userError s!"{name}: {error}")
  unless accepted > 0 && accepted < cases.length do
    throw (IO.userError "encoded-regex acceptance/rejection coverage")
  -- Literal expectations also pin the boundary semantics independently of the oracle.
  checkLiteral ⟨[]⟩ [] false
  checkLiteral ⟨[.epsilon]⟩ [] true
  checkLiteral ⟨[.char false, .char true, .comp 0 1]⟩ [false, true] true
  checkLiteral ⟨[.char false, .char true, .comp 0 1]⟩ [true, false] false
  checkLiteral ⟨[.star 0]⟩ [] true
  checkLiteral ⟨[.star 0]⟩ [false] false
  checkLiteral ⟨[.char true, .plus 0 1]⟩ [true] true
  checkLiteral ⟨[.char false, .zero]⟩ [false] false
  IO.println s!"encoded-regex seed=2026111801 fixed={fixed.length} words={words.length} generated={inputs.length}"
  IO.println s!"encoded-regex agreement={cases.length} accepted={accepted} rejected={cases.length - accepted} literals=8"
  IO.println s!"encoded-regex roots={roots} nodeCounts={sizes} wordLengths={lengths} letters={letters}"
  IO.println "encoded-regex retries=0 discards=0; finite Bool fixtures, not a universal proof"

#eval runMembershipTests

end Cslib.Language.EncodedRegex.RuntimeTests
