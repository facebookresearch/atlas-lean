/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# INTERVAL GRAPH SANDWICH: definitions

Source:
M. C. Golumbic and R. Shamir, "Complexity and algorithms for reasoning about time: a
graph-theoretic approach", Journal of the ACM 40 (1993), 1108-1133, doi:10.1145/174147.169675
("the interval graph sandwich problem is introduced, and is shown to be NP-complete");
M. C. Golumbic, H. Kaplan, and R. Shamir, "On the complexity of DNA physical mapping",
Advances in Applied Mathematics 15 (1994), 251-261, doi:10.1006/aama.1994.1009.
-/
module

public import CSLibExt.Computability.Complexity.Defs
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Computability.Complexity.Karp.Color
public import CSLibExt.Complexity.NPComplete.IntervalGraphCompletionDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.IntervalGraphSandwich

open MetaMathlibExt.Complexity.NPComplete.IntervalGraphCompletion (IsIntervalGraph)

/-- An instance: vertex count `n` (vertices `Fin n`), the edge list `E₁` of the required edges,
and the edge list `E₂` of the allowed edges. -/
abbrev IntervalGraphSandwichInstance := ℕ × List (ℕ × ℕ) × List (ℕ × ℕ)

/-- The graph `G₁ = (V, E₁)` of required edges as a `SimpleGraph (Fin n)`. -/
def Lower (i : IntervalGraphSandwichInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.1

/-- The graph `G₂ = (V, E₂)` of allowed edges as a `SimpleGraph (Fin n)`. -/
def Upper (i : IntervalGraphSandwichInstance) : SimpleGraph (Fin i.1) :=
  Cslib.Complexity.Karp.edgeGraph i.1 i.2.2

/-- Well-formedness of an instance: both edge lists describe simple graphs on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and every edge of
`E₁` is an edge of `E₂`, in either orientation. -/
def WellFormed (i : IntervalGraphSandwichInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    (i.2.2.Nodup ∧ ∀ e ∈ i.2.2, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.2) ∧
    ∀ e ∈ i.2.1, e ∈ i.2.2 ∨ (e.2, e.1) ∈ i.2.2

/-- Some interval graph `H` on the same vertices contains every required edge and only allowed
edges. -/
def IntervalGraphSandwichFeasible (i : IntervalGraphSandwichInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), Lower i ≤ H ∧ H ≤ Upper i ∧ IsIntervalGraph H

open Classical in
/-- INTERVAL GRAPH SANDWICH as a decision problem over bitstrings. -/
noncomputable def intervalGraphSandwichDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalGraphSandwichInstance) x with
  | some i => decide (WellFormed i ∧ IntervalGraphSandwichFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.IntervalGraphSandwich
