/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# STRONG EDGE COLORING: definitions

Source:
M. Mahdian, "On the computational complexity of strong edge coloring", Discrete Applied
Mathematics 118 (2002), 239-248, doi:10.1016/S0166-218X(01)00237-2;
H. Hocquard, P. Ochem and P. Valicov, "Strong edge-colouring and induced matchings",
Information Processing Letters 113 (2013), 836-843, doi:10.1016/j.ipl.2013.07.026.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.EdgeColoringDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.StrongEdgeColoring

open MetaMathlibExt.Complexity.NPComplete.EdgeColoring (EdgeColoringInstance WellFormed)

/-- The edges `e` and `f` (vertex pairs) are within distance one in the graph with edge list
`es`: they share an endpoint, or some edge of `es` joins an endpoint of `e` to an endpoint of
`f`. -/
def Near (es : List (ℕ × ℕ)) (e f : ℕ × ℕ) : Prop :=
  e.1 = f.1 ∨ e.1 = f.2 ∨ e.2 = f.1 ∨ e.2 = f.2 ∨
    ∃ g ∈ es, ((g.1 = e.1 ∨ g.1 = e.2) ∧ (g.2 = f.1 ∨ g.2 = f.2)) ∨
      ((g.2 = e.1 ∨ g.2 = e.2) ∧ (g.1 = f.1 ∨ g.1 = f.2))

/-- A strong edge coloring with at most `K` colors: one color below `K` per listed edge, distinct
on any two distinct positions whose edges are `Near`. -/
def StrongEdgeColoringFeasible (i : EdgeColoringInstance) : Prop :=
  ∃ coloring : List ℕ, coloring.length = i.2.1.length ∧ (∀ c ∈ coloring, c < i.2.2) ∧
    ∀ a < i.2.1.length, ∀ b < i.2.1.length, a ≠ b →
      Near i.2.1 (i.2.1.getD a (0, 0)) (i.2.1.getD b (0, 0)) →
        coloring.getD a 0 ≠ coloring.getD b 0

open Classical in
/-- STRONG EDGE COLORING as a decision problem over bitstrings. -/
noncomputable def strongEdgeColoringDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := EdgeColoringInstance) x with
  | some i => decide (WellFormed i ∧ StrongEdgeColoringFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.StrongEdgeColoring
