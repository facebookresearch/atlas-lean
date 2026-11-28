/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PATHWIDTH: definitions

Source:
T. Ohtsuki, H. Mori, E. S. Kuh, T. Kashiwabara and T. Fujisawa, "One-dimensional logic gate
assignment and interval graphs", IEEE Transactions on Circuits and Systems 26 (1979), 675-684,
doi:10.1109/TCS.1979.1084695 (minimum clique number interval augmentation is NP-complete);
T. Kashiwabara and T. Fujisawa, "NP-completeness of the problem of finding a minimum-clique-number
interval graph containing a given graph as a subgraph", Proc. IEEE International Symposium on
Circuits and Systems (1979), 657-660.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.PathwidthChordalGraphsDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.Pathwidth

open MetaMathlibExt.Complexity.NPComplete.PathwidthChordalGraphs
  (PathwidthChordalGraphsInstance PathwidthChordalGraphsFeasible)

/-- Well-formedness of an instance: the edge list describes a simple graph on `Fin n` (no
duplicate edges in either orientation, no self-loops, endpoints in range), and `0 < K`. -/
def WellFormed (i : PathwidthChordalGraphsInstance) : Prop :=
  (i.2.1.Nodup ∧ ∀ e ∈ i.2.1, e.1 < i.1 ∧ e.2 < i.1 ∧ e.1 ≠ e.2 ∧ (e.2, e.1) ∉ i.2.1) ∧
    0 < i.2.2

open Classical in
/-- PATHWIDTH as a decision problem over bitstrings. -/
noncomputable def pathwidthDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PathwidthChordalGraphsInstance) x with
  | some i => decide (WellFormed i ∧ PathwidthChordalGraphsFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.Pathwidth
