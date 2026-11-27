/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Computability.Complexity.Karp.MinOnesThreeSat

/-!
# Minimum-ones 3-SAT decision examples

These examples exercise the weight bound and the treatment of malformed instances.
-/

namespace MetaMathlibExt.Complexity.NPComplete.MinOnesThreeSat.Tests

open BitstringEncoding Cslib.Logic.LegacyPL

private def accepts (i : MinOnesThreeSatInstance) := minOnesThreeSatDec (bitEncode i) = true

private theorem accepts_iff (i : MinOnesThreeSatInstance) :
    accepts i ↔ WellFormed i ∧ MinOnesThreeSatFeasible i := by
  simp [accepts, minOnesThreeSatDec, bitDecode_bitEncode]

private def positive : CNF := [[(0, true), (0, true), (0, true)]]

-- Three occurrences of the same positive literal cost one true variable.
example : accepts (1, positive, 1) := by
  apply (accepts_iff _).mpr
  refine ⟨?_, [true], rfl, ?_, by decide⟩
  · simp [WellFormed, positive]
  · simp [positive, CNF.Satisfies, CNFClause.Satisfies]

example : ¬ accepts (1, positive, 0) := by
  rintro h
  obtain ⟨_, a, ha, hs, hk⟩ := (accepts_iff _).mp h
  change a.length = 1 at ha
  obtain ⟨b, rfl⟩ := List.length_eq_one_iff.mp ha
  cases b <;> simp [positive, CNF.Satisfies, CNFClause.Satisfies] at *

-- An empty formula needs no true variables, even with an arbitrarily large declared range.
private theorem empty_accepts (n : Nat) : accepts (n, [], 0) := by
  apply (accepts_iff _).mpr
  refine ⟨by simp [WellFormed], List.replicate n false, by simp, by simp, ?_⟩
  simp

example : ¬ accepts (1, [[(0, true)]], 1) := by
  simp [accepts_iff, WellFormed]

example : ¬ accepts (0, positive, 1) := by
  simp [accepts_iff, WellFormed, positive]

-- The noncanonical first field [false] decodes to 2, just like [false, true].
example : minOnesThreeSatDec [true, false, false, false] = true := by
  have hd : bitDecode (α := MinOnesThreeSatInstance) [true, false, false, false] =
      some (2, [], 0) := by decide
  simpa [minOnesThreeSatDec, hd] using (accepts_iff _).mp (empty_accepts 2)

example : minOnesThreeSatDec [] = false := by
  rfl

end MetaMathlibExt.Complexity.NPComplete.MinOnesThreeSat.Tests
