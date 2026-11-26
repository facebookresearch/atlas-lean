/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import CSLibExt.Computability.Complexity.Karp.MonotoneThreeSat

/-! Boundary cases for the encoded MONOTONE 3-SAT language. -/

namespace MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Tests

open BitstringEncoding Cslib.Logic.LegacyPL

private def pos : CNFClause := [(0, true), (0, true), (0, true)]
private def neg : CNFClause := [(0, false), (0, false), (0, false)]

-- A repeated literal is legal. Two clauses forcing opposite values are inconsistent.
example : monotoneThreeSatDec (bitEncode ((1, [pos]) : MonotoneThreeSatInstance)) = true := by
  classical
  simp only [monotoneThreeSatDec, bitDecode_bitEncode, decide_eq_true_eq]
  refine ⟨by simp [WellFormed, pos], [true], rfl, ?_⟩
  simp [pos]

example : monotoneThreeSatDec (bitEncode ((1, [pos, neg]) : MonotoneThreeSatInstance)) = false := by
  classical
  simp only [monotoneThreeSatDec, bitDecode_bitEncode, decide_eq_false_iff_not]
  rintro ⟨_, a, _, ha⟩
  simp [pos, neg] at ha

-- Mixed signs, a variable at the exclusive upper bound, and a short clause are malformed.
example : ¬ WellFormed (1, [[(0, true), (0, false), (0, true)]]) := by simp [WellFormed]
example : ¬ WellFormed (0, [neg]) := by simp [WellFormed, neg]
example : ¬ WellFormed (1, [[(0, true)]]) := by simp [WellFormed]

-- An unframed input is rejected. A noncanonical binary header still decodes.
example : monotoneThreeSatDec [] = false := rfl

example : monotoneThreeSatDec [true, false, false] = true := by
  classical
  change decide (WellFormed (2, []) ∧ MonotoneThreeSatFeasible (2, [])) = true
  exact decide_eq_true ⟨by simp [WellFormed], [false, false], rfl, by simp⟩

end MetaMathlibExt.Complexity.NPComplete.MonotoneThreeSat.Tests
