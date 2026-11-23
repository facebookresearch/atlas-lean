/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.MachineLearning.PACLearning.Growth
-- Required by the runtime #guard and #eval clients, not visible to shake.
meta import CSLibExt.MachineLearning.PACLearning.Growth -- shake: keep

/-! Executable tests of finite traces, with an independent bitmask oracle. -/

open Cslib.MachineLearning.PACLearning

namespace CSLibExtTest.MachineLearning.PACLearning

private def sample (n mask : ℕ) : Finset ℕ :=
  (Finset.range n).filter fun x => mask.testBit x = true

private def hypotheses (n family : ℕ) : List (ℕ → Bool) :=
  ((List.range (2 ^ n)).filter family.testBit).map Nat.testBit

private def oracleCount (n family sampleMask : ℕ) : ℕ :=
  (((List.range (2 ^ n)).filter family.testBit).map
    (fun h => h &&& sampleMask)).eraseDups.length

-- Duplicate functions and functions differing only outside the sample.
#guard (finiteTraces [fun _ : ℕ => false, fun _ => false,
  fun x => x == 7] {0, 1}).card == 1
#guard (finiteTraces [fun _ : ℕ => false, fun x => x == 0,
  fun x => x == 7] {0, 1}).card == 2
#guard (finiteTraces ([] : List (ℕ → Bool)) {0, 1}).card == 0
#guard (finiteTraces ([] : List (ℕ → Bool)) ∅).card == 0
#guard (finiteTraces [fun _ : ℕ => false, fun _ => true] ∅).card == 1
#guard (finiteTraces (hypotheses 3 255) {0, 1, 2}).card == 8
#guard (finiteTraces (hypotheses 3 255) {0, 2}).card == 4

/-- info: [0, 1, 2, 4, 8] -/
#guard_msgs in
#eval [
  (finiteTraces ([] : List (ℕ → Bool)) {0}).card,
  (finiteTraces [fun _ : ℕ => true] ∅).card,
  (finiteTraces (hypotheses 1 3) {0}).card,
  (finiteTraces (hypotheses 2 15) {0, 1}).card,
  (finiteTraces (hypotheses 3 255) {0, 1, 2}).card]

private def bitCount (n mask : ℕ) : ℕ :=
  ((List.range n).filter mask.testBit).length

private def oracleDimension (n family sampleMask : ℕ) : ℕ :=
  (List.range (2 ^ n)).foldl (fun d sub =>
    if sub &&& sampleMask == sub &&
        oracleCount n family sub == 2 ^ bitCount n sub then
      max d (bitCount n sub)
    else d) 0

private def checkSmallDomains : IO Unit := do
  let mut families := 0
  let mut pairs := 0
  for n in List.range 4 do
    for family in List.range (2 ^ (2 ^ n)) do
      families := families + 1
      let H := hypotheses n family
      let d := oracleDimension n family (2 ^ n - 1)
      for mask in List.range (2 ^ n) do
        pairs := pairs + 1
        let s := sample n mask
        let traces := finiteTraces H s
        let expected := oracleCount n family mask
        unless traces.card == expected && s.card == bitCount n mask do
          throw <| IO.userError s!"trace mismatch: {n}, {family}, {mask}"
        unless traces.vcDim == oracleDimension n family mask do
          throw <| IO.userError s!"dimension mismatch: {n}, {family}, {mask}"
        let bound := ((List.range (d + 1)).map s.card.choose).sum
        unless traces.card ≤ bound do
          throw <| IO.userError s!"bound mismatch: {n}, {family}, {mask}"
  unless families == 278 && pairs == 2122 do
    throw <| IO.userError s!"enumeration incomplete: {families}, {pairs}"
  IO.println s!"checked {families} classes and {pairs} class/sample pairs"

/-- info: checked 278 classes and 2122 class/sample pairs -/
#guard_msgs in
#eval checkSmallDomains

end CSLibExtTest.MachineLearning.PACLearning
