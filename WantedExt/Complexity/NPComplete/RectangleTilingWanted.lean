/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# RECTANGLE TILING is NP-complete

Source:
S. Khanna, S. Muthukrishnan and M. Paterson, "On approximating rectangle tiling and packing",
Proceedings of the Ninth Annual ACM-SIAM Symposium on Discrete Algorithms (SODA 1998), 384-393
(Section 1.1, problem RTILE; Theorem 2.1: RTILE is NP-hard even with element weights that are
non-negative integers bounded by a constant, by a reduction from PLANAR-3SAT); research report
version: Department of Computer Science Research Report CS-RR-339, University of Warwick (1998);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems*, entry MINIMUM
RECTANGLE TILING.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Prod
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.RectangleTiling

/-!
# RECTANGLE TILING is NP-complete

INSTANCE: an `n × n` array `A` of non-negative numbers, a positive integer `p` and a positive
integer `K`.
QUESTION: is there a partition of `A` into at most `p` non-overlapping rectangular subarrays
(rectangles that cover `A` without overlap) such that the weight of every rectangle, the sum of
the array elements that fall within it, is at most `K`?

This is the decision version of Khanna, Muthukrishnan and Paterson's rectangle tiling problem
RTILE (Section 1.1: "Given an `n × n` array `A` of non-negative numbers, partition it into at most
`p` rectangular subarrays (that is, the rectangles cover `A` without overlap) such that the
maximum weight of any rectangle is minimized"), in the form of the Crescenzi-Kann compendium
entry MINIMUM RECTANGLE TILING (`p` and the bound `K` positive integers; the compendium writes
"a partition of `A` into `p` non-overlapping rectangular subarrays", and the primary source's "at
most `p`" is followed here). Theorem 2.1 shows that
it is NP-hard already when the elements are non-negative integers bounded by a constant (its
reduction produces instances with elements in `{1, …, 4}` and `K = 4`); here the elements are
non-negative integers. Membership in NP: a tiling assigns each of the `n²` cells one of at most
`p` rectangles, a certificate of polynomial size.

The array is given by its rows, each a list of `n` elements, where `n` is the number of rows;
cell `(r, c)` (`r, c : Fin n`) holds the `c`-th element of the `r`-th row. A partition into at most
`p` rectangles is a map `g` from the cells to `Fin p` whose classes `g⁻¹(j)` are rectangles: for
each `j` there are bounds `r₁, r₂, c₁, c₂` such that `g x = j` exactly for the cells `x` with
`r₁ ≤ x.1 ≤ r₂` and `c₁ ≤ x.2 ≤ c₂` (an unused index has an empty class). The weight of class
`j` is the sum of the elements of its cells. All numbers use the canonical binary encoding.

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the rows of the array `A`, the number `p` of rectangles and the weight bound
`K`. -/
abbrev RectangleTilingInstance := List (List ℕ) × ℕ × ℕ

/-- The side `n` of the array: its number of rows. -/
abbrev side (i : RectangleTilingInstance) : ℕ := i.1.length

/-- The element `A[r][c]` of the array. -/
def entry (i : RectangleTilingInstance) (x : Fin (side i) × Fin (side i)) : ℕ :=
  (i.1.getD x.1 []).getD x.2 0

/-- Well-formedness of an instance: the array is square (every row has `n` elements), and `p`
and `K` are positive. -/
def WellFormed (i : RectangleTilingInstance) : Prop :=
  (∀ row ∈ i.1, row.length = side i) ∧ 0 < i.2.1 ∧ 0 < i.2.2

/-- Some partition of the cells into at most `p` rectangles gives every rectangle weight at most
`K`. -/
def RectangleTilingFeasible (i : RectangleTilingInstance) : Prop :=
  ∃ g : Fin (side i) × Fin (side i) → Fin i.2.1,
    (∀ j, ∃ r₁ r₂ c₁ c₂ : ℕ, ∀ x,
      g x = j ↔ (r₁ ≤ x.1 ∧ (x.1 : ℕ) ≤ r₂ ∧ c₁ ≤ x.2 ∧ (x.2 : ℕ) ≤ c₂)) ∧
    ∀ j, (∑ x ∈ Finset.univ.filter (fun x => g x = j), entry i x) ≤ i.2.2

open Classical in
/-- RECTANGLE TILING as a decision problem over bitstrings. -/
noncomputable def rectangleTilingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := RectangleTilingInstance) x with
  | some i => decide (WellFormed i ∧ RectangleTilingFeasible i)
  | none => false

/-- **RECTANGLE TILING is NP-complete.** Source: Khanna, Muthukrishnan and Paterson (1998),
Theorem 2.1 (hardness); the certificate of the module docstring gives membership in NP. -/
public theorem_wanted rectangleTiling_npComplete :
    rectangleTilingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L rectangleTilingDec

end MetaMathlibExt.Complexity.NPComplete.RectangleTiling
