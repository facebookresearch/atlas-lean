/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# HASHIWOKAKERO is NP-complete

Source:
D. Andersson, "Hashiwokakero is NP-complete", Information Processing Letters 109(19) (2009),
1145-1146, doi:10.1016/j.ipl.2009.07.017.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Hashiwokakero

/-!
# HASHIWOKAKERO (BRIDGES) is NP-complete

INSTANCE: a finite set of islands at integer grid points, each labelled with an integer in
`{1, …, 8}`.
QUESTION: can horizontal and vertical bridges be drawn between islands, at most two between a
pair, with no crossings, so that each island has exactly its label's number of bridges and the
bridges connect the islands into a single connected group?

The islands are listed as `(x, y, ℓ)`: position `(x, y)` and label `ℓ`. Positions are natural
numbers; any finite set of integer grid points can be translated into this quadrant, which
changes nothing in the puzzle. A solution gives every pair of islands `a, b` a number of bridges
`bridges a b = bridges b a ≤ 2`. A bridge runs straight between two distinct islands in the same
row or the same column, and may not pass over another island (`Visible`): no island lies
strictly between its ends on its line. A horizontal and a vertical bridge cross when each passes
strictly between the ends of the other (`Cross`); two bridges on one line cannot overlap without
passing over an island, so this is the only way bridges cross. The islands are connected when
the graph joining islands with at least one bridge between them is preconnected (any two islands
are joined by a chain of bridges); the island set is nonempty (`WellFormed`), so this is a
single connected group.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the islands `(x, y, ℓ)`, at position `(x, y)` with label `ℓ`. -/
abbrev HashiwokakeroInstance := List (ℕ × ℕ × ℕ)

/-- Well-formedness of an instance: there is at least one island, islands are at distinct
positions, and every label is in `{1, …, 8}`. -/
def WellFormed (i : HashiwokakeroInstance) : Prop :=
  i ≠ [] ∧ (i.map fun t => (t.1, t.2.1)).Nodup ∧ ∀ t ∈ i, 1 ≤ t.2.2 ∧ t.2.2 ≤ 8

/-- The `x`-coordinate (column) of the island at index `a`. -/
def X (i : HashiwokakeroInstance) (a : Fin i.length) : ℕ := (i.get a).1

/-- The `y`-coordinate (row) of the island at index `a`. -/
def Y (i : HashiwokakeroInstance) (a : Fin i.length) : ℕ := (i.get a).2.1

/-- The label of the island at index `a`. -/
def Label (i : HashiwokakeroInstance) (a : Fin i.length) : ℕ := (i.get a).2.2

/-- A bridge can join the islands at indices `a` and `b`: they are distinct, in the same row or
the same column, and no island lies strictly between them on that line. -/
def Visible (i : HashiwokakeroInstance) (a b : Fin i.length) : Prop :=
  a ≠ b ∧
    ((Y i a = Y i b ∧ ∀ c, Y i c = Y i a →
        ¬ (min (X i a) (X i b) < X i c ∧ X i c < max (X i a) (X i b))) ∨
      (X i a = X i b ∧ ∀ c, X i c = X i a →
        ¬ (min (Y i a) (Y i b) < Y i c ∧ Y i c < max (Y i a) (Y i b))))

/-- The horizontal bridge between `a` and `b` and the vertical bridge between `c` and `d` cross:
each passes strictly between the ends of the other. -/
def Cross (i : HashiwokakeroInstance) (a b c d : Fin i.length) : Prop :=
  Y i a = Y i b ∧ X i c = X i d ∧
    min (X i a) (X i b) < X i c ∧ X i c < max (X i a) (X i b) ∧
    min (Y i c) (Y i d) < Y i a ∧ Y i a < max (Y i c) (Y i d)

/-- Some bridge counts `bridges a b` (symmetric, at most `2`, positive only between islands that
see each other, no two crossing bridges) give every island exactly its label's number of bridges
and connect all islands. -/
def HashiwokakeroFeasible (i : HashiwokakeroInstance) : Prop :=
  ∃ bridges : Fin i.length → Fin i.length → ℕ,
    (∀ a b, bridges a b = bridges b a) ∧ (∀ a b, bridges a b ≤ 2) ∧
    (∀ a b, 0 < bridges a b → Visible i a b) ∧
    (∀ a b c d, 0 < bridges a b → 0 < bridges c d → ¬ Cross i a b c d) ∧
    (∀ a, ∑ b, bridges a b = Label i a) ∧
    (SimpleGraph.fromRel fun a b => 0 < bridges a b).Preconnected

open Classical in
/-- HASHIWOKAKERO as a decision problem over bitstrings. -/
noncomputable def hashiwokakeroDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := HashiwokakeroInstance) x with
  | some i => decide (WellFormed i ∧ HashiwokakeroFeasible i)
  | none => false

/-- **HASHIWOKAKERO is NP-complete.** Source: Andersson (2009). -/
public theorem_wanted hashiwokakero_npComplete :
    hashiwokakeroDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L hashiwokakeroDec

end MetaMathlibExt.Complexity.NPComplete.Hashiwokakero
