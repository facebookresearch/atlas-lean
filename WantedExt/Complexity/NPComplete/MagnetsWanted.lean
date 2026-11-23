/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAGNETS is NP-complete

Source:
J. Kölker, "The Magnets puzzle is NP-complete", Journal of Information Processing 20(3)
(2012), 707-708, doi:10.2197/ipsjjip.20.707 (Section 1, Theorem 1).
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Sign.Defs
public import Mathlib.Combinatorics.SimpleGraph.Hasse
public import Mathlib.Combinatorics.SimpleGraph.Prod

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Magnets

/-!
# MAGNETS is NP-complete

Kölker's Magnets puzzle. INSTANCE: a `w × h` rectangle, a subdivision of this rectangle into
dominoes, and `2(w + h)` integers `rᵢ⁺, rᵢ⁻, cⱼ⁺, cⱼ⁻` for `i = 0, …, h - 1` and
`j = 0, …, w - 1`. QUESTION: can a value in `{-1, 0, +1}` be assigned to each square such that
(1) the two values in each domino sum to `0`; (2) every pair `(x, y)` of horizontally or
vertically adjacent values satisfies `x = y = 0 ∨ x ≠ y`; and (3) in each row `i`, `+1`
occurs `rᵢ⁺` times and `-1` occurs `rᵢ⁻` times, and in each column `j`, `+1` occurs `cⱼ⁺`
times and `-1` occurs `cⱼ⁻` times?

Squares are pairs `(i, j)` of a row `i < h` and a column `j < w`; adjacency is the grid
graph `pathGraph h □ pathGraph w`. Values are Mathlib's `SignType` (`-1`, `0`, `1`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance `(w, h, D, R, C)`: the width `w`, the height `h`, the dominoes `D` (each a
pair of squares `(row, column)`), the row counts `R = [(r₀⁺, r₀⁻), …]` (one pair per row) and
the column counts `C = [(c₀⁺, c₀⁻), …]` (one pair per column). -/
abbrev MagnetsInstance :=
  ℕ × ℕ × List ((ℕ × ℕ) × (ℕ × ℕ)) × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- The grid graph of the rectangle: squares `(i, j)` with `i < h`, `j < w`, adjacent when
horizontally or vertically adjacent. -/
def Grid (i : MagnetsInstance) : SimpleGraph (Fin i.2.1 × Fin i.1) :=
  SimpleGraph.pathGraph i.2.1 □ SimpleGraph.pathGraph i.1

/-- A square of the grid as a pair of natural numbers `(row, column)`. -/
def toNatPair {h w : ℕ} (a : Fin h × Fin w) : ℕ × ℕ := ((a.1 : ℕ), (a.2 : ℕ))

/-- Well-formedness of an instance `(w, h, D, R, C)`: there are `h` row counts and `w` column
counts, every domino is a pair of adjacent squares of the grid, and the dominoes subdivide the
rectangle (every square lies in exactly one domino). -/
def WellFormed (i : MagnetsInstance) : Prop :=
  i.2.2.2.1.length = i.2.1 ∧ i.2.2.2.2.length = i.1 ∧
    (∀ d ∈ i.2.2.1, ∃ a b : Fin i.2.1 × Fin i.1,
      toNatPair a = d.1 ∧ toNatPair b = d.2 ∧ (Grid i).Adj a b) ∧
    (i.2.2.1.flatMap fun d => [d.1, d.2]).Perm
      ((List.range i.2.1).flatMap fun r => (List.range i.1).map fun c => (r, c))

/-- Some assignment of `-1`, `0`, `+1` to the squares satisfies rules (1)-(3). -/
def MagnetsFeasible (i : MagnetsInstance) : Prop :=
  ∃ v : Fin i.2.1 × Fin i.1 → SignType,
    (∀ d ∈ i.2.2.1, ∀ a b : Fin i.2.1 × Fin i.1,
      toNatPair a = d.1 → toNatPair b = d.2 → (v a : ℤ) + (v b : ℤ) = 0) ∧
    (∀ a b, (Grid i).Adj a b → (v a = 0 ∧ v b = 0) ∨ v a ≠ v b) ∧
    (∀ r : Fin i.2.1,
      (Finset.univ.filter fun c => v (r, c) = 1).card = (i.2.2.2.1.getD r (0, 0)).1 ∧
        (Finset.univ.filter fun c => v (r, c) = -1).card = (i.2.2.2.1.getD r (0, 0)).2) ∧
    ∀ c : Fin i.1,
      (Finset.univ.filter fun r => v (r, c) = 1).card = (i.2.2.2.2.getD c (0, 0)).1 ∧
        (Finset.univ.filter fun r => v (r, c) = -1).card = (i.2.2.2.2.getD c (0, 0)).2

open Classical in
/-- MAGNETS as a decision problem over bitstrings. -/
noncomputable def magnetsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MagnetsInstance) x with
  | some i => decide (WellFormed i ∧ MagnetsFeasible i)
  | none => false

/-- **MAGNETS is NP-complete.** Source: Kölker (2012), Theorem 1 (membership: a solution is
a certificate; hardness: a reduction from monotone 1-in-3 satisfiability). -/
public theorem_wanted magnets_npComplete :
    magnetsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L magnetsDec

end MetaMathlibExt.Complexity.NPComplete.Magnets
