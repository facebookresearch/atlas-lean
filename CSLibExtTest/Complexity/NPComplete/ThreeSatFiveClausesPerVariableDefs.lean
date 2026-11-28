/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/
module

import CSLibExt.Complexity.NPComplete.ThreeSatFiveClausesPerVariableDefs

namespace MetaMathlibExt.Complexity.NPComplete.ThreeSatFiveClausesPerVariable

open MetaMathlibExt.BitstringEncoding (bitDecode bitDecode_bitEncode bitEncode)

private theorem accepts_encoding (i : ThreeSatFiveClausesPerVariableInstance) :
    threeSatFiveClausesPerVariableDec (bitEncode i) = true ↔
      WellFormed i ∧ ThreeSatFiveClausesPerVariableFeasible i := by
  simp [threeSatFiveClausesPerVariableDec, bitDecode_bitEncode]

/-- A lone continuation bit is a truncated instance encoding. -/
example : threeSatFiveClausesPerVariableDec [true] = false := by
  have h : bitDecode (α := ThreeSatFiveClausesPerVariableInstance) [true] = none := rfl
  simp [threeSatFiveClausesPerVariableDec, h]

/-- `(x₀ ∨ x₁ ∨ x₂) ∧ (¬x₀ ∨ ¬x₁ ∨ x₂) ∧ (x₀ ∨ ¬x₁ ∨ ¬x₂)` is satisfied by
`x₀ = true`, `x₁ = false`, `x₂ = false`. -/
example :
    threeSatFiveClausesPerVariableDec
      (bitEncode ((3, [[(0, true), (1, true), (2, true)], [(0, false), (1, false), (2, true)],
        [(0, true), (1, false), (2, false)]]) : ThreeSatFiveClausesPerVariableInstance)) =
          true := by
  apply (accepts_encoding _).2
  refine ⟨by unfold WellFormed; decide, [true, false, false], rfl, ?_⟩
  unfold Cslib.Logic.LegacyPL.CNF.Satisfies Cslib.Logic.LegacyPL.CNFClause.Satisfies
    Cslib.Logic.LegacyPL.CNFLiteral.Satisfies
  decide

/-- A satisfiable formula in which variable `0` occurs in six clauses. -/
private abbrev sixOccurrences : ThreeSatFiveClausesPerVariableInstance :=
  (3, [[(0, true), (1, true), (2, true)], [(0, true), (1, true), (2, false)],
    [(0, true), (1, false), (2, true)], [(0, true), (1, false), (2, false)],
    [(0, false), (1, true), (2, true)], [(0, false), (1, false), (2, false)]])

/-- The six-occurrence formula is satisfiable, by `x₀ = true`, `x₁ = true`,
`x₂ = false`. -/
example : ThreeSatFiveClausesPerVariableFeasible sixOccurrences :=
  ⟨[true, true, false], rfl, by
    unfold Cslib.Logic.LegacyPL.CNF.Satisfies Cslib.Logic.LegacyPL.CNFClause.Satisfies
      Cslib.Logic.LegacyPL.CNFLiteral.Satisfies
    decide⟩

/-- The six-occurrence formula is rejected: the occurrence bound of five fails. -/
example : threeSatFiveClausesPerVariableDec (bitEncode sixOccurrences) = false := by
  rw [Bool.eq_false_iff, ne_eq, accepts_encoding]
  rintro ⟨h, -⟩
  revert h
  unfold WellFormed
  decide

end MetaMathlibExt.Complexity.NPComplete.ThreeSatFiveClausesPerVariable
