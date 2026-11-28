/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# ONE-SIDED CROSSING MINIMIZATION: definitions

Source:
P. Eades and N. C. Wormald, "Edge crossings in drawings of bipartite graphs", Algorithmica 11(4)
(1994), 379-403, doi:10.1007/BF01187020;
X. Muñoz, W. Unger and I. Vrt'o, "One sided crossing minimization is NP-hard for sparse graphs",
Graph Drawing (GD 2001), LNCS 2265 (2002), 115-123, doi:10.1007/3-540-45848-4_10.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OneSidedCrossingMinimization

/-- An instance: the vertices of `U` in their fixed order, the vertices of `W`, the edges
`(u, w)`, and the bound `K`. -/
abbrev OneSidedCrossingMinimizationInstance := List ℕ × List ℕ × List (ℕ × ℕ) × ℕ

/-- The number of crossings of the two-layer drawing with `U` in the order `U` and `W` in the
order `order`: ordered pairs of edges `((u₁, w₁), (u₂, w₂))` with `u₁` before `u₂` and `w₂` before
`w₁`. -/
def crossings (U order : List ℕ) (E : List (ℕ × ℕ)) : ℕ :=
  (E.product E).countP fun p =>
    U.idxOf p.1.1 < U.idxOf p.2.1 ∧ order.idxOf p.2.2 < order.idxOf p.1.2

/-- Well-formedness of an instance: `U` and `W` are listed without repetition, and the edges are
listed without repetition and join a vertex of `U` to a vertex of `W`. -/
def WellFormed (i : OneSidedCrossingMinimizationInstance) : Prop :=
  i.1.Nodup ∧ i.2.1.Nodup ∧ i.2.2.1.Nodup ∧ ∀ e ∈ i.2.2.1, e.1 ∈ i.1 ∧ e.2 ∈ i.2.1

/-- Some linear order of `W` gives a two-layer drawing with at most `K` crossings. -/
def OneSidedCrossingMinimizationFeasible (i : OneSidedCrossingMinimizationInstance) : Prop :=
  ∃ order : List ℕ, order.Perm i.2.1 ∧ crossings i.1 order i.2.2.1 ≤ i.2.2.2

open Classical in
/-- ONE-SIDED CROSSING MINIMIZATION as a decision problem over bitstrings. -/
noncomputable def oneSidedCrossingMinimizationDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OneSidedCrossingMinimizationInstance) x with
  | some i => decide (WellFormed i ∧ OneSidedCrossingMinimizationFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OneSidedCrossingMinimization
