/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# MAP LABELING WITH FOUR POSITIONS is NP-complete

Source:
M. Formann and F. Wagner, "A packing problem with applications to lettering of maps", in
*Proceedings of the 7th Annual Symposium on Computational Geometry (SoCG 1991)*, ACM (1991),
281-288, doi:10.1145/109648.109680.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MapLabelingFourPosition

/-!
# MAP LABELING WITH FOUR POSITIONS is NP-complete

INSTANCE: a finite set of points in the plane with integer coordinates and a positive rational
`σ`.
QUESTION: can each point be labeled by an axis-parallel `σ × σ` square that has the point as one
of its four corners, such that no two labels overlap (their interiors are disjoint; labels may
touch)?

The points are a duplicate-free list of integer pairs, each integer given as a pair
`(positive part, negative part)` of natural numbers as in `ZeroOneILPWanted`; `σ = p / q` with
`p, q > 0`. A labeling chooses for each point `(x, y)` a corner `(a, b) ∈ {0, 1}²`, and its label
is the square with lower-left corner `(x - aσ, y - bσ)`. Two open `σ × σ` squares with lower-left
corners `(u, v)` and `(u', v')` intersect iff `|u - u'| < σ` and `|v - v'| < σ`; multiplying by
`q`, the labels of points `j ≠ k` are disjoint iff `|q(xⱼ - xₖ) - p(aⱼ - aₖ)| ≥ p` or
`|q(yⱼ - yₖ) - p(bⱼ - bₖ)| ≥ p` (`AtLeast`). Binary encoding of all numbers.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the points, each coordinate an integer as `(positive part, negative part)`, and
`σ = p / q` as the pair `(p, q)`. -/
abbrev MapLabelingFourPositionInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ × ℕ

/-- The integer `a - b` encoded by `(a, b)`. -/
def toInt (z : ℕ × ℕ) : ℤ := (z.1 : ℤ) - z.2

/-- The points as integer pairs. -/
def points (i : MapLabelingFourPositionInstance) : List (ℤ × ℤ) :=
  i.1.map fun pt => (toInt pt.1, toInt pt.2)

/-- Well-formedness of an instance: no point is listed twice and `p, q > 0`. -/
def WellFormed (i : MapLabelingFourPositionInstance) : Prop :=
  (points i).Nodup ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- `|d| ≥ p`. -/
def AtLeast (p : ℕ) (d : ℤ) : Prop := (p : ℤ) ≤ d ∨ d ≤ -(p : ℤ)

/-- Some choice of corners `(a, b) ∈ {0, 1}²` gives pairwise non-overlapping labels. -/
def MapLabelingFourPositionFeasible (i : MapLabelingFourPositionInstance) : Prop :=
  ∃ a b : Fin (points i).length → Fin 2, ∀ j k : Fin (points i).length, j ≠ k →
    AtLeast i.2.1 ((i.2.2 : ℤ) * ((points i)[j].1 - (points i)[k].1) -
        (i.2.1 : ℤ) * (((a j : ℕ) : ℤ) - ((a k : ℕ) : ℤ))) ∨
      AtLeast i.2.1 ((i.2.2 : ℤ) * ((points i)[j].2 - (points i)[k].2) -
        (i.2.1 : ℤ) * (((b j : ℕ) : ℤ) - ((b k : ℕ) : ℤ)))

open Classical in
/-- MAP LABELING WITH FOUR POSITIONS as a decision problem over bitstrings. -/
noncomputable def mapLabelingFourPositionDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := MapLabelingFourPositionInstance) x with
  | some i => decide (WellFormed i ∧ MapLabelingFourPositionFeasible i)
  | none => false

/-- **MAP LABELING WITH FOUR POSITIONS is NP-complete.** Source: Formann and Wagner (1991). -/
public theorem_wanted mapLabelingFourPosition_npComplete :
    mapLabelingFourPositionDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L mapLabelingFourPositionDec

end MetaMathlibExt.Complexity.NPComplete.MapLabelingFourPosition
