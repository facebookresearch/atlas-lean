/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.Complexity
public meta import MathlibExt.Computability.Complexity

/-!
# Runtime tests for concrete bitstring codecs

Finite Bool, pair and list cases check exact encoder bits, decoder grammar, parser
payloads and remainders, and block fuel boundaries. Direct templates and a marker scan
provide expected observations; these checks make no complexity or generic-codec claim.
-/

@[expose] public section

namespace MathlibExtTest.Computability.BitstringEncodingRuntimeTests

open MetaMathlibExt.BitstringEncoding

private def bitstrings (bound : Nat) : List (List Bool) :=
  (List.range (bound + 1)).flatMap (fun size =>
    (List.range (2 ^ size)).map (fun mask =>
      (List.range size).map (fun i => mask / 2 ^ (size - 1 - i) % 2 == 1)))

private def boolGrammar : List Bool → Option Bool
  | [value] => some value
  | _ => none

private def pairGrammar : List Bool → Option (Bool × Bool)
  | [true, first, false, second] => some (first, second)
  | _ => none

private def listGrammar (bits : List Bool) : Option (List Bool) :=
  let input := bits.toArray
  let positions := List.range (bits.length / 3)
  if bits.length % 3 != 0 then none
  else if positions.all (fun i =>
      input[3 * i]? == some true && input[3 * i + 2]? == some false) then
    some (positions.map (fun i => input[3 * i + 1]?.getD false))
  else none

-- The first false at an even marker position ends a block; odd positions are payload.
private def blockGrammar (bits : List Bool) : Option (List Bool × List Bool) := do
  let (_, stop) ← bits.zipIdx.find? (fun (bit, i) => !bit && i % 2 == 0)
  let payload := (bits.take stop).zipIdx.filterMap
    (fun (bit, i) => if i % 2 == 1 then some bit else none)
  return (payload, bits.drop (stop + 1))

private def blocksGrammar (bits : List Bool) : Option (List (List Bool)) := do
  let initial : Option (List (List Bool) × List Bool) := some ([], bits)
  let (blocks, rest) ← (List.range bits.length).foldl (fun state _ => do
    let (blocks, rest) ← state
    if rest.isEmpty then return (blocks, rest)
    let (payload, tail) ← blockGrammar rest
    return (blocks ++ [payload], tail)) initial
  if rest.isEmpty then return blocks else none

private def frameBits (payload : List Bool) : List Bool :=
  payload.flatMap (fun bit => [true, bit]) ++ [false]

private def listBits (values : List Bool) : List Bool :=
  values.flatMap (fun bit => [true, bit, false])

private def observe {α : Type} [BEq α] [Repr α] (label : String)
    (actual expected : α) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError <| s!"observation mismatch: {label}, actual={reprStr actual}, " ++
      s!"expected={reprStr expected}"
  IO.println s!"PASS {label}: actual={reprStr actual}, expected={reprStr expected}"

private def rejectObservation {α : Type} [BEq α] [Repr α] (label : String)
    (actual wrong expected : α) : IO Unit := do
  observe s!"baseline {label}" actual expected
  unless wrong != expected do throw <| IO.userError s!"wrong observation was accepted: {label}"
  IO.println s!"REJECT {label}: wrong={reprStr wrong}, expected={reprStr expected}"

private def nestedCases : List (List (List Bool) × List Bool) :=
  [([[], []], [false, false]),
    ([[], [false, true]],
      [false, true, true, true, false, true, false, true, true, true, true, true, false, false]),
    ([[true], []], [true, true, true, true, true, false, false, false])]

private def fuelCases : List (Nat × List Bool × Option (List (List Bool))) :=
  [(0, [], some []), (0, [false], none), (1, [false], some [[]]),
    (1, [false, false], none), (2, [false, false], some [[], []]),
    (1, [true, true, false], some [[true]]),
    (1, [true, true, false, false], none),
    (2, [true, true, false, false], some [[true], []])]

private def runTests : IO Unit := do
  let raw := bitstrings 7
  unless raw.length == 255 && decide raw.Nodup do
    throw <| IO.userError "raw corpus mismatch"
  let mut accepted : List Nat := [0, 0, 0, 0, 0]
  for (bits, i) in raw.zipIdx do
    IO.println s!"RAW {i}: input={bits}"
    let boolean := bitDecode (α := Bool) bits
    let pair := bitDecode (α := Bool × Bool) bits
    let values := bitDecode (α := List Bool) bits
    let block := undelimit bits
    let blocks := undelimitBlocks bits
    observe s!"raw Bool {i}" boolean (boolGrammar bits)
    observe s!"raw PairBool {i}" pair (pairGrammar bits)
    observe s!"raw ListBool {i}" values (listGrammar bits)
    observe s!"raw Block {i}" block (blockGrammar bits)
    observe s!"raw Blocks {i}" blocks (blocksGrammar bits)
    accepted := accepted.zipWith
      (fun count ok => count + if ok then 1 else 0)
      [boolean.isSome, pair.isSome, values.isSome, block.isSome, blocks.isSome]
  IO.println "RAW passed=255, typed-decoders=3, parsers=2"
  IO.println s!"ACCEPTED Bool/PairBool/ListBool/Block/Blocks={accepted}"
  IO.println s!"REJECTED Bool/PairBool/ListBool/Block/Blocks={accepted.map (255 - ·)}"

  observe "remainder anchor" (undelimit [true, true, false, false])
    (some ([true], [false]))

  for ((fuel, bits, expected), i) in fuelCases.zipIdx do
    IO.println s!"FUEL {i}: fuel={fuel}, input={bits}"
    observe s!"fuel {i}" (undelimitBlocksAux fuel bits) expected
  IO.println "FUEL passed=8"

  for value in [false, true] do
    observe s!"encode Bool {value}" (bitEncode value) [value]
    observe s!"decode Bool {value}" (bitDecode (α := Bool) (bitEncode value)) (some value)
  for first in [false, true] do
    for second in [false, true] do
      let value := (first, second)
      observe s!"encode PairBool {first} {second}" (bitEncode value) [true, first, false, second]
      observe s!"decode PairBool {first} {second}"
        (bitDecode (α := Bool × Bool) (bitEncode value)) (some value)
  for (value, i) in (bitstrings 3).zipIdx do
    observe s!"encode ListBool {i}" (bitEncode value) (listBits value)
    observe s!"decode ListBool {i}" (bitDecode (α := List Bool) (bitEncode value)) (some value)
  for ((value, bits), i) in nestedCases.zipIdx do
    observe s!"encode NestedListBool {i}" (bitEncode value) bits
    observe s!"decode NestedListBool {i}"
      (bitDecode (α := List (List Bool)) (bitEncode value)) (some value)
  IO.println "ENCODERS passed=24, Bool=2, PairBool=4, ListBool=15, NestedListBool=3"

  let mut prefixes := 0
  for payload in bitstrings 3 do
    for suffix in bitstrings 2 do
      IO.println s!"PREFIX {prefixes}: payload={payload}, suffix={suffix}"
      observe s!"prefix encoding {prefixes}" (delimit payload) (frameBits payload)
      observe s!"prefix parse {prefixes}" (undelimit (delimit payload ++ suffix))
        (some (payload, suffix))
      prefixes := prefixes + 1
  unless prefixes == 105 do throw <| IO.userError "prefix corpus mismatch"
  IO.println "PREFIXES passed=105, extra-remainder-anchor=1"

  rejectObservation "wrong Bool encoding" (bitEncode false) [true] [false]
  rejectObservation "lost suffix" (undelimit [true, true, false, false])
    (some ([true], [])) (some ([true], [false]))
  rejectObservation "truncated PairBool accepted" (bitDecode (α := Bool × Bool) [true])
    (some (false, false)) none
  rejectObservation "fuel overflow accepted" (undelimitBlocksAux 1 [false, false])
    (some [[], []]) none
  IO.println "CONTROLS rejected=4, real-same-input-baselines=4"

#eval runTests

end MathlibExtTest.Computability.BitstringEncodingRuntimeTests
