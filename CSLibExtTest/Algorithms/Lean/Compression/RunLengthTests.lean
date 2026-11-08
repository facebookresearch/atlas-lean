/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.Algorithms.Lean.Compression.RunLength
public meta import CSLibExt.Algorithms.Lean.Compression.RunLength

/-!
# Run-length encoding execution tests

The documented 15/7/7/11 example, empty input, a 300-bit run split at 255,
and alternating bits, each in both directions where the source fixes them.
-/

namespace CSLibExtTest.Algorithms.Compression

open Cslib.Algorithms.Lean.RunLength

private meta def verifyCounts (label : String) (actual expected : List Nat) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: returned {actual}, expected {expected}"

private meta def verifyBits (label : String) (actual expected : List Bool) : IO Unit := do
  unless actual == expected do
    throw <| IO.userError s!"{label}: returned {actual}, expected {expected}"

private meta def runTests : IO Unit := do
  let documented : List Bool :=
    List.replicate 15 false ++ List.replicate 7 true ++ List.replicate 7 false ++
      List.replicate 11 true
  verifyCounts "documented compress" (compress documented) [15, 7, 7, 11]
  verifyBits "documented expand" (expand [15, 7, 7, 11]) documented
  IO.println "documented: 15 zeros, 7 ones, 7 zeros, 11 ones both directions "

  verifyCounts "empty compress" (compress []) [0]
  verifyBits "empty expand" (expand [0]) []
  verifyBits "no counts expand" (expand []) []
  IO.println "empty: compress [0], expand [] "

  verifyCounts "split compress" (compress (List.replicate 300 false)) [255, 0, 45]
  verifyBits "split expand" (expand [255, 0, 45]) (List.replicate 300 false)
  IO.println "split: 300 zeros as [255, 0, 45] both directions "

  let alternating : List Bool := [true, false, true, false]
  verifyCounts "alternating compress" (compress alternating) [0, 1, 1, 1, 1]
  verifyBits "alternating expand" (expand [0, 1, 1, 1, 1]) alternating
  IO.println "alternating: leading zero run emitted both directions"

#eval runTests

end CSLibExtTest.Algorithms.Compression
