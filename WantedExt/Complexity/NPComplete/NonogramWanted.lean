/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# NONOGRAM is NP-complete

Source:
N. Ueda and T. Nagao, "NP-completeness results for nonogram via parsimonious reductions"
(1996).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Nonogram

/-!
# NONOGRAM is NP-complete

Row and column run-length clues for a two-color picture. The question is whether there is a
picture (rows of Booleans) whose rows and columns have exactly the given runs of consecutive
true cells, where runs are the maximal blocks of true cells in order.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A nonogram instance: row run-length clues, column run-length clues. -/
abbrev NonogramInstance := List (List ℕ) × List (List ℕ)


/-- One step of the run computation: current run length and completed runs. -/
def RunsStep (b : Bool) (acc : ℕ × List ℕ) : ℕ × List ℕ :=
  if b then (acc.1 + 1, acc.2) else (0, if acc.1 = 0 then acc.2 else acc.1 :: acc.2)

/-- The run lengths of a row: maximal blocks of consecutive true cells. -/
def Runs (l : List Bool) : List ℕ :=
  let acc := l.foldr RunsStep (0, [])
  if acc.1 = 0 then acc.2 else acc.1 :: acc.2


/-- A picture matching all row and column run clues. -/
def NonogramFeasible
    (i : NonogramInstance) : Prop :=
  ∃ picture : List (List Bool), picture.length = i.1.length ∧
    (∀ row ∈ picture, row.length = i.2.length) ∧
    (∀ r < i.1.length, Runs (picture.getD r []) = i.1.getD r []) ∧
    ∀ c < i.2.length, Runs ((List.range picture.length).map
      (fun r => (picture.getD r []).getD c false)) = i.2.getD c []

open Classical in
/-- NONOGRAM as a decision problem over bitstrings. -/
noncomputable def nonogramDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := NonogramInstance) x with
  | some i => decide (NonogramFeasible i)
  | none => false

/-- **NONOGRAM is NP-complete.** Source: N. Ueda and T. Nagao, "NP-completeness results for
nonogram via parsimonious reductions" (1996). -/
public theorem_wanted nonogram_npComplete :
    nonogramDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L nonogramDec

end MetaMathlibExt.Complexity.NPComplete.Nonogram
