/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# COMPARABILITY GRAPH SANDWICH: definitions

Source:
M. C. Golumbic, H. Kaplan and R. Shamir, "Graph sandwich problems", Journal of Algorithms 19(3)
(1995), 449-473, doi:10.1006/jagm.1995.1047.
-/
module

public import Mathlib.Order.Defs.Unbundled
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.IntervalGraphSandwichDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ComparabilityGraphSandwich

/-- `H` is a comparability graph: some strict partial order `r` on the vertices makes two
vertices adjacent exactly when they are comparable (`r` orients each edge transitively). -/
def IsComparabilityGraph {V : Type*} (H : SimpleGraph V) : Prop :=
  ∃ r : V → V → Prop, IsStrictOrder V r ∧ ∀ u v, H.Adj u v ↔ r u v ∨ r v u

/-- Some comparability graph `H` on the same vertices contains every required edge and only
allowed edges. -/
def ComparabilityGraphSandwichFeasible
    (i : IntervalGraphSandwich.IntervalGraphSandwichInstance) : Prop :=
  ∃ H : SimpleGraph (Fin i.1), IntervalGraphSandwich.Lower i ≤ H ∧
    H ≤ IntervalGraphSandwich.Upper i ∧ IsComparabilityGraph H

open Classical in
/-- COMPARABILITY GRAPH SANDWICH as a decision problem over bitstrings. -/
noncomputable def comparabilityGraphSandwichDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := IntervalGraphSandwich.IntervalGraphSandwichInstance) x with
  | some i => decide (IntervalGraphSandwich.WellFormed i ∧ ComparabilityGraphSandwichFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ComparabilityGraphSandwich
