/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PACKING WITH DISCS is NP-complete

Source:
D. S. Johnson, "The NP-completeness column: an ongoing guide", J. Algorithms 3 (1982), 182-195,
doi:10.1016/0196-6774(82)90018-9, problem [14] PACKING WITH SQUARES, comment;
R. J. Fowler, M. S. Paterson and S. L. Tanimoto, "Optimal packing and covering in the plane are
NP-complete", Information Processing Letters 12 (1981), 133-137,
doi:10.1016/0020-0190(81)90111-3.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Basic.Real.Basic
public import WantedExt.Complexity.NPComplete.PackingSquaresRectilinearPolygonWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PackingWithDiscs

/-!
# PACKING WITH DISCS is NP-complete

Johnson's column states PACKING WITH SQUARES (INSTANCE: a rectilinear, not necessarily simply
connected polygon `P`, positive integers `d` and `K`; QUESTION: can `K` disjoint `d × d` squares
be placed inside `P` with their sides parallel to the axes?) for the application of cutting
`2 × 2` blocks out of the functioning chips of a wafer, whose functioning parts "together form
what is essentially a union of rectilinear polygons", and adds: "The problem of packing such an
area with identical discs is also NP-complete" (Fowler, Paterson and Tanimoto 1981). This is the
disc version:

INSTANCE: a rectilinear polygon `P` (holes allowed) and positive integers `d` and `K`.
QUESTION: can `K` non-overlapping discs of diameter `d` be placed inside `P`?

The instance and its well-formedness are those of `PackingSquaresRectilinearPolygon`, reused
here: the side `d` (here the diameter), the list of unit cells `[a, a + 1] × [b, b + 1]` of the
grid forming `P` (a polyomino, holes allowed), and `K`. A disc of diameter `d` is placed with
its center anywhere in the plane `ℝ × ℝ`; it lies inside `P` when every point at Euclidean
distance at most `d / 2` from its center lies in one of the cells. Two discs do not overlap
when their interiors are disjoint, i.e. their centers are at Euclidean distance at least `d`.
Distances are written out as sums of squares, since `dist` on `ℝ × ℝ` is the sup distance.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

open PackingSquaresRectilinearPolygon

/-- The point `p` lies in the polygon: in some cell `[a, a + 1] × [b, b + 1]` of it. -/
def InPolygon (i : PackingSquaresRectilinearPolygonInstance) (p : ℝ × ℝ) : Prop :=
  ∃ q ∈ i.2.1, (q.1 : ℝ) ≤ p.1 ∧ p.1 ≤ q.1 + 1 ∧ (q.2 : ℝ) ≤ p.2 ∧ p.2 ≤ q.2 + 1

/-- `K` discs of diameter `d` with centers `c j` lie in the polygon and do not overlap. -/
def PackingWithDiscsFeasible (i : PackingSquaresRectilinearPolygonInstance) : Prop :=
  ∃ c : Fin i.2.2 → ℝ × ℝ,
    (∀ j, ∀ p : ℝ × ℝ, (p.1 - (c j).1) ^ 2 + (p.2 - (c j).2) ^ 2 ≤ ((i.1 : ℝ) / 2) ^ 2 →
      InPolygon i p) ∧
    ∀ j j', j ≠ j' → (i.1 : ℝ) ^ 2 ≤ ((c j).1 - (c j').1) ^ 2 + ((c j).2 - (c j').2) ^ 2

open Classical in
/-- PACKING WITH DISCS as a decision problem over bitstrings. -/
noncomputable def packingWithDiscsDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PackingSquaresRectilinearPolygonInstance) x with
  | some i => decide (WellFormed i ∧ PackingWithDiscsFeasible i)
  | none => false

/-- **PACKING WITH DISCS is NP-complete.** Source: Johnson (1982), problem [14], comment;
Fowler, Paterson and Tanimoto (1981). -/
public theorem_wanted packingWithDiscs_npComplete :
    packingWithDiscsDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L packingWithDiscsDec

end MetaMathlibExt.Complexity.NPComplete.PackingWithDiscs
