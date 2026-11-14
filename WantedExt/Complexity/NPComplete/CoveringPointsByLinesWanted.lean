/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COVERING POINTS BY LINES is NP-complete

Source:
N. Megiddo and A. Tamir, "On the complexity of locating linear facilities in the plane",
Operations Research Letters 1 (1982), 194-197, doi:10.1016/0167-6377(82)90039-6;
P. K. Agarwal, C. M. Procopiuc and K. R. Varadarajan, "Approximation algorithms for k-line
center", Algorithms - ESA 2002, LNCS 2461 (2002), 54-63, doi:10.1007/3-540-45749-6_9.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
public import WantedExt.Complexity.NPComplete.GeometricTravelingSalesmanWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.CoveringPointsByLines

open GeometricTravelingSalesman (point)

/-!
# COVERING POINTS BY LINES is NP-complete

INSTANCE: a finite set `P` of points in the plane with integer coordinates, and a positive
integer `K`. QUESTION: can the points of `P` be covered by at most `K` straight lines, that is,
are there `K` lines in the plane such that every point of `P` lies on one of them?

Megiddo and Tamir prove that finding `r` lines minimizing any isotone function of the distances
from the given points to their nearest lines is NP-hard in the strong sense; covering the points
by `K` lines is the case where every distance is `0`. Agarwal, Procopiuc and Varadarajan (§1,
"Previous results") record the decision form: Megiddo and Tamir "showed that it is NP-complete to
decide whether a set of points in the plane can be covered by `k` lines".

The points are listed explicitly, each as a pair of integer coordinates, each integer a pair
`(p, q)` of naturals standing for `p - q`, decoded by `GeometricTravelingSalesman.point` (reused
from `GeometricTravelingSalesmanWanted`). `P` is a set, so the decoded points are distinct. A
point `(x, y)` is placed in the real plane `ℝ × ℝ`; a straight line is Mathlib's
`line[ℝ, a, b]` (the affine span of two distinct points `a ≠ b`). A family of `K` lines may
repeat a line, so "at most `K` lines" is a family indexed by `Fin K`. A bound `K ≥ |P|` makes
the answer trivially yes.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the points, each a pair of integer coordinates in positive/negative-part
form, and the bound `K`. -/
abbrev CoveringPointsByLinesInstance := List ((ℕ × ℕ) × (ℕ × ℕ)) × ℕ

/-- Well-formedness of an instance: the points are distinct, and `K` is positive. -/
def WellFormed (i : CoveringPointsByLinesInstance) : Prop :=
  (i.1.map point).Nodup ∧ 0 < i.2

/-- There are `K` straight lines, each through two distinct points of `ℝ × ℝ`, such that every
point of `P` lies on one of them. -/
def CoveringPointsByLinesFeasible (i : CoveringPointsByLinesInstance) : Prop :=
  ∃ L : Fin i.2 → (ℝ × ℝ) × (ℝ × ℝ), (∀ j, (L j).1 ≠ (L j).2) ∧
    ∀ q ∈ i.1, ∃ j, ((point q).map Int.cast Int.cast : ℝ × ℝ) ∈ line[ℝ, (L j).1, (L j).2]

open Classical in
/-- COVERING POINTS BY LINES as a decision problem over bitstrings. -/
noncomputable def coveringPointsByLinesDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := CoveringPointsByLinesInstance) x with
  | some i => decide (WellFormed i ∧ CoveringPointsByLinesFeasible i)
  | none => false

/-- **COVERING POINTS BY LINES is NP-complete.** Source: Megiddo and Tamir (1982); recorded in
Agarwal, Procopiuc and Varadarajan (2002). -/
public theorem_wanted coveringPointsByLines_npComplete :
    coveringPointsByLinesDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L coveringPointsByLinesDec

end MetaMathlibExt.Complexity.NPComplete.CoveringPointsByLines
