/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED SHISEN-SHO: definitions

Source:
C. Iwamoto, Y. Wada and K. Morita, "Generalized Shisen-Sho is NP-Complete", IEICE Transactions
on Information and Systems E95-D(11) (2012), 2712-2715, doi:10.1587/transinf.E95.D.2712.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ShisenSho

/-- An instance: the initial layout, a list of `R` rows of `C` tile labels each. -/
abbrev ShisenShoInstance := List (List ℕ)

/-- The cells of the board, as integer points `(row, column)`. -/
def cells (i : ShisenShoInstance) : List (ℤ × ℤ) :=
  (List.range i.length).flatMap fun r =>
    (List.range (i.getD 0 []).length).map fun c => ((r : ℤ), (c : ℤ))

/-- The label of the tile at a board cell. -/
def label (i : ShisenShoInstance) (p : ℤ × ℤ) : ℕ :=
  (i.getD p.1.toNat []).getD p.2.toNat 0

/-- The lattice point `q` lies on the axis-parallel segment from `p` to `p'`. -/
def OnSegment (p p' q : ℤ × ℤ) : Prop :=
  (p.1 = p'.1 ∧ q.1 = p.1 ∧ min p.2 p'.2 ≤ q.2 ∧ q.2 ≤ max p.2 p'.2) ∨
    (p.2 = p'.2 ∧ q.2 = p.2 ∧ min p.1 p'.1 ≤ q.1 ∧ q.1 ≤ max p.1 p'.1)

/-- The points `a` and `b` can be connected with at most three orthogonal line segments that
cross no tile: there is a path `a → p₁ → p₂ → b` of axis-parallel segments (degenerate segments
allowed, so one or two segments also qualify) none of whose lattice points other than `a` and
`b` is occupied. -/
def Connectable (occupied : ℤ × ℤ → Prop) (a b : ℤ × ℤ) : Prop :=
  ∃ p₁ p₂ : ℤ × ℤ, (a.1 = p₁.1 ∨ a.2 = p₁.2) ∧ (p₁.1 = p₂.1 ∨ p₁.2 = p₂.2) ∧
    (p₂.1 = b.1 ∨ p₂.2 = b.2) ∧
    ∀ q, (OnSegment a p₁ q ∨ OnSegment p₁ p₂ q ∨ OnSegment p₂ b q) → q ≠ a → q ≠ b →
      ¬ occupied q

/-- Well-formedness: the layout is a nonempty rectangle (every row as long as the first, which
is nonempty) and every label occurring in it occurs exactly four times. -/
def WellFormed (i : ShisenShoInstance) : Prop :=
  i ≠ [] ∧ i.getD 0 [] ≠ [] ∧ (∀ row ∈ i, row.length = (i.getD 0 []).length) ∧
    ∀ l ∈ i.flatten, i.flatten.count l = 4

/-- All tiles can be removed: a sequence of pairs, removed in order, in which every tile occurs
exactly once, the two tiles of each pair have the same label, and they can be connected while
exactly the tiles of the earlier pairs are gone. -/
def ShisenShoFeasible (i : ShisenShoInstance) : Prop :=
  ∃ pairs : List ((ℤ × ℤ) × (ℤ × ℤ)),
    (pairs.flatMap fun s => [s.1, s.2]).Perm (cells i) ∧
    ∀ t (ht : t < pairs.length),
      label i pairs[t].1 = label i pairs[t].2 ∧
      Connectable
        (fun q => q ∈ cells i ∧ q ∉ (pairs.take t).flatMap fun s => [s.1, s.2])
        pairs[t].1 pairs[t].2

open Classical in
/-- GENERALIZED SHISEN-SHO as a decision problem over bitstrings. -/
noncomputable def shisenShoDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ShisenShoInstance) x with
  | some i => decide (WellFormed i ∧ ShisenShoFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ShisenSho
