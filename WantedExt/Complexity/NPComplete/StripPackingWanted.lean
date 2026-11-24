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

/-- **Strip packing instances.** A strip packing instance is a triple $(R, W, H)$ consisting of a
finite list $R = ((w_1, h_1), \dots, (w_n, h_n))$ of pairs of natural numbers, the widths and
heights of the rectangles, a natural number $W$, the width of the strip, and a natural number $H$,
the height bound. -/
abbrev StripPackingInstance := List (ℕ × ℕ) × ℕ × ℕ

/-- **Well-formed strip packing instances.** A strip packing instance $(R, W, H)$ is well formed
when every rectangle $(w, h)$ in the list $R$ has $w > 0$ and $h > 0$. -/
def WellFormed (i : StripPackingInstance) : Prop :=
  ∀ r ∈ i.1, 0 < r.1 ∧ 0 < r.2

/-- **Feasible strip packings.** A strip packing instance $(R, W, H)$ with
$R = ((w_1, h_1), \dots, (w_n, h_n))$ is feasible when there are natural numbers
$x_1, y_1, \dots, x_n, y_n$ such that $x_j + w_j \le W$ and $y_j + h_j \le H$ for every
$1 \le j \le n$, and for all $1 \le a < b \le n$ at least one of $x_a + w_a \le x_b$,
$x_b + w_b \le x_a$, $y_a + h_a \le y_b$ and $y_b + h_b \le y_a$ holds.

That is, the unrotated rectangles with lower-left corners $(x_j, y_j)$, widths $w_j$ and heights
$h_j$ lie in $[0, W] \times [0, H]$, and any two of them are separated by a vertical or a
horizontal line. When all widths and heights are positive, the latter says that no two of the
rectangles overlap in their interiors. -/
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
/-- **The STRIP PACKING decision problem.** STRIP PACKING is the decision problem that accepts a
bitstring $x$ exactly when $x$ decodes, under the canonical bitstring encoding of strip packing
instances, to a strip packing instance that is well formed and feasible. Bitstrings that do not
decode to a strip packing instance are rejected. -/
noncomputable def stripPackingDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := StripPackingInstance) x with
  | some i => decide (WellFormed i ∧ StripPackingFeasible i)
  | none => false

/-- **STRIP PACKING is NP-complete.** The STRIP PACKING decision problem belongs to NP, and every
decision problem $L$ in NP reduces to STRIP PACKING by a polynomial-time many-one reduction.

Source: M. R. Garey and D. S. Johnson, *Computers and
Intractability* (1979), STRIP PACKING (axis-aligned, no rotations). -/
public theorem_wanted stripPacking_npComplete :
    stripPackingDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L stripPackingDec

end MetaMathlibExt.Complexity.NPComplete.StripPacking
