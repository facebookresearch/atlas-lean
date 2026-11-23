/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPEN HEMISPHERE is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP6] OPEN HEMISPHERE;
D. S. Johnson and F. P. Preparata, "The densest hemisphere problem", Theoretical
Computer Science 6 (1978), 93-107, doi:10.1016/0304-3975(78)90006-3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Ring.Rat

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OpenHemisphere

/-!
# OPEN HEMISPHERE is NP-complete

INSTANCE: a finite set `X` of `m`-tuples of integers, and a positive integer `K ≤ |X|`.
QUESTION: is there an `m`-tuple `y` of rational numbers such that `x · y > 0` for at least `K`
`m`-tuples `x ∈ X`?

Each integer is encoded as a pair of naturals `(positive part, negative part)` representing their
difference (`intOf`), as in `WantedExt.Complexity.NPComplete.ZeroOneILPWanted`; numbers use the
canonical binary encoding. `X` is a list; since `X` is a set, `WellFormed` requires the decoded
integer tuples to be pairwise distinct, so the length of the list is `|X|` and the count of
tuples with `x · y > 0` is a count of elements of `X`.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the length `m` of the tuples, the list `X` of `m`-tuples of encoded integers,
and the bound `K`. -/
abbrev OpenHemisphereInstance := ℕ × List (List (ℕ × ℕ)) × ℕ

/-- The integer `p.1 - p.2` encoded by a pair of naturals. -/
def intOf (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) - (p.2 : ℤ)

/-- Well-formedness of an instance: every element of `X` is an `m`-tuple, the decoded integer
tuples are pairwise distinct (`X` is a set), and `0 < K ≤ |X|`. -/
def WellFormed (i : OpenHemisphereInstance) : Prop :=
  (∀ x ∈ i.2.1, x.length = i.1) ∧ (i.2.1.map fun x => x.map intOf).Nodup ∧
    0 < i.2.2 ∧ i.2.2 ≤ i.2.1.length

/-- A rational `m`-tuple `y` with `x · y > 0` for at least `K` elements `x` of `X`. -/
def OpenHemisphereFeasible (i : OpenHemisphereInstance) : Prop :=
  ∃ y : Fin i.1 → ℚ, i.2.2 ≤
    (i.2.1.filter fun x => 0 < ∑ j : Fin i.1, (intOf (x.getD j (0, 0)) : ℚ) * y j).length

open Classical in
/-- OPEN HEMISPHERE as a decision problem over bitstrings. -/
noncomputable def openHemisphereDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OpenHemisphereInstance) x with
  | some i => decide (WellFormed i ∧ OpenHemisphereFeasible i)
  | none => false

/-- **OPEN HEMISPHERE is NP-complete.** Source: Garey and Johnson (1979), [MP6]; Johnson and
Preparata (1978). -/
public theorem_wanted openHemisphere_npComplete :
    openHemisphereDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L openHemisphereDec

end MetaMathlibExt.Complexity.NPComplete.OpenHemisphere
