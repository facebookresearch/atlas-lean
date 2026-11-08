/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRIP PACKING is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability* (1979), STRIP PACKING (axis-
aligned, no rotations).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StripPacking

/-!
# STRIP PACKING is NP-complete

Axis-aligned rectangles with integer dimensions, a strip of width `W`, and a height bound `H`.
The question is whether the rectangles can be placed at integer coordinates inside the strip
without overlap, with no rotations. Rectangles must have positive width and height: degenerate
zero-area items are malformed.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- A strip-packing instance: rectangles (width, height), strip width, height bound. -/
abbrev StripPackingInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- Well-formedness of an instance. -/
def WellFormed (i : StripPackingInstance) : Prop :=
  ∀ r ∈ i.1, 0 < r.1 ∧ 0 < r.2

/-- A non-overlapping placement inside the strip. -/
def StripPackingFeasible
    (i : StripPackingInstance) : Prop :=
  ∃ placements : List (ℕ × ℕ), placements.length = i.1.length ∧
    (∀ j < i.1.length, (placements.getD j (0, 0)).1 + (i.1.getD j (0, 0)).1 ≤ i.2.1 ∧
      (placements.getD j (0, 0)).2 + (i.1.getD j (0, 0)).2 ≤ i.2.2) ∧
    ∀ a < i.1.length, ∀ b < i.1.length, a < b →
      (placements.getD a (0, 0)).1 + (i.1.getD a (0, 0)).1 ≤ (placements.getD b (0, 0)).1 ∨
      (placements.getD b (0, 0)).1 + (i.1.getD b (0, 0)).1 ≤ (placements.getD a (0, 0)).1 ∨
      (placements.getD a (0, 0)).2 + (i.1.getD a (0, 0)).2 ≤ (placements.getD b (0, 0)).2 ∨
      (placements.getD b (0, 0)).2 + (i.1.getD b (0, 0)).2 ≤ (placements.getD a (0, 0)).2

open Classical in
/-- STRIP PACKING as a decision problem over bitstrings. -/
noncomputable def stripPackingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StripPackingInstance) x with
  | some i => decide (WellFormed i ∧ StripPackingFeasible i)
  | none => false

/-- **STRIP PACKING is NP-complete.** Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), STRIP PACKING (axis-aligned, no rotations). -/
public theorem_wanted stripPacking_npComplete :
    stripPackingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stripPackingDec

end MetaMathlibExt.Complexity.NPComplete.StripPacking
