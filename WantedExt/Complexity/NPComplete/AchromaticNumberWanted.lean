/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ACHROMATIC NUMBER is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), ACHROMATIC NUMBER; M.
Farber et al., "The achromatic number of graphs" (1986).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.AchromaticNumber

/-!
# ACHROMATIC NUMBER is NP-complete

An undirected graph and a bound `K`. The question is whether the achromatic number is at least
`K`: a proper coloring using some number `q ≥ K` of colors (colors `0, …, q - 1`, all used)
such that every pair of used colors appears on some edge.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: vertex count, edge list, bound. -/
abbrev AchromaticNumberInstance := ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : AchromaticNumberInstance) : Prop :=
  i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1

/-- A complete coloring with at least `K` used colors. -/
def AchromaticNumberFeasible
    (i : AchromaticNumberInstance) : Prop :=
  ∃ q : ℕ, i.2.2 ≤ q ∧
    ∃ coloring : List ℕ, coloring.length = i.1 ∧ (∀ v < i.1, coloring.getD v 0 < q) ∧
    (∀ c < q, ∃ v < i.1, coloring.getD v 0 = c) ∧
    (∀ e ∈ i.2.1, coloring.getD e.1 0 ≠ coloring.getD e.2 0) ∧
    ∀ a < q, ∀ b < q, a ≠ b → ∃ e ∈ i.2.1,
      (coloring.getD e.1 0 = a ∧ coloring.getD e.2 0 = b) ∨
      (coloring.getD e.1 0 = b ∧ coloring.getD e.2 0 = a)

open Classical in
/-- ACHROMATIC NUMBER as a decision problem over bitstrings. -/
noncomputable def achromaticNumberDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AchromaticNumberInstance) x with
  | some i => decide (WellFormed i ∧ AchromaticNumberFeasible i)
  | none => false

/-- **ACHROMATIC NUMBER is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers
and Intractability* (1979), ACHROMATIC NUMBER; M. Farber et al., "The achromatic number of
graphs" (1986). -/
public theorem_wanted achromaticNumber_npComplete :
    achromaticNumberDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L achromaticNumberDec

end MetaMathlibExt.Complexity.NPComplete.AchromaticNumber
