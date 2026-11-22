/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# AKARI (LIGHT UP) is NP-complete

Source:
Brandon McPhail, "Light Up is NP-complete", unpublished manuscript, 2005.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity


@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Akari

/-!
# AKARI (LIGHT UP) is NP-complete

A board of cells: `0` empty, `1` wall, `2 + k` a numbered wall requiring exactly `k`
orthogonally adjacent bulbs. The question is whether bulbs can be placed on empty cells so that
every empty cell is illuminated (a bulb shines along its row and column until a wall), no bulb
illuminates another bulb, and every numbered wall has exactly the indicated number of
orthogonally adjacent bulbs.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An Akari instance: board (0 empty, 1 wall, 2+k numbered wall k). -/
abbrev AkariInstance := List (List ℕ)


/-- A bulb at `(br, bc)` illuminates cell `(r, c)`: same row or column, no wall between. -/
def Illuminates (board : List (List ℕ)) (br bc r c : ℕ) : Prop :=
  (br = r ∧ ∀ cc, (min bc c < cc ∧ cc < max bc c) →
    (board.getD r []).getD cc 1 = 0) ∨
  (bc = c ∧ ∀ rr, (min br r < rr ∧ rr < max br r) →
    (board.getD rr []).getD c 1 = 0)


/-- Well-formedness of an instance. -/
def WellFormed (i : AkariInstance) : Prop :=
  ∀ row ∈ i, ∀ x ∈ row, x ≤ 6 ∧ ∀ row ∈ i, row.length = (i.getD 0 []).length

/-- A bulb placement illuminating every empty cell, respecting numbered walls. -/
def AkariFeasible
    (i : AkariInstance) : Prop :=
  ∃ bulbs : List (ℕ × ℕ), bulbs.Nodup ∧
    (∀ p ∈ bulbs, p.1 < i.length ∧ p.2 < (i.getD 0 []).length ∧
      (i.getD p.1 []).getD p.2 1 = 0) ∧
    (∀ r < i.length, ∀ c < (i.getD 0 []).length, (i.getD r []).getD c 1 = 0 →
      ∃ b ∈ bulbs, Illuminates i b.1 b.2 r c) ∧
    (∀ b ∈ bulbs, ∀ b' ∈ bulbs, b ≠ b' → ¬ Illuminates i b.1 b.2 b'.1 b'.2) ∧
    ∀ r < i.length, ∀ c < (i.getD 0 []).length, 2 ≤ (i.getD r []).getD c 1 →
      ((bulbs.filter (fun b => (b.1 == r + 1 && b.2 == c) || (b.1 + 1 == r && b.2 == c) ||
        (b.1 == r && b.2 == c + 1) || (b.1 == r && b.2 + 1 == c))).length =
        (i.getD r []).getD c 1 - 2)

open Classical in
/-- AKARI (LIGHT UP) as a decision problem over bitstrings. -/
noncomputable def akariDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := AkariInstance) x with
  | some i => decide (WellFormed i ∧ AkariFeasible i)
  | none => false

/-- **AKARI (LIGHT UP) is NP-complete.** Source: Brandon McPhail, "Light Up is NP-complete",
unpublished manuscript, 2005. -/
public theorem_wanted akari_npComplete :
    akariDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L akariDec

end MetaMathlibExt.Complexity.NPComplete.Akari
