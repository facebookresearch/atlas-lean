/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# METRIC TRAVELING SALESPERSON: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [ND22] TRAVELING SALESMAN, comment:
"Remains NP-complete even if d(cᵢ, cⱼ) ∈ {1, 2} for all cᵢ, cⱼ ∈ C" (transformation from
HAMILTONIAN CIRCUIT);
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), MINIMUM METRIC TRAVELING SALESPERSON PROBLEM.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.TspDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.MetricTravelingSalesperson

open Tsp (TspInstance TspFeasible)

/-- Well-formedness of an instance: a well-formed TRAVELING SALESPERSON instance (a symmetric
`m × m` distance matrix with zero diagonal, `0 < m`) whose distances between distinct cities are
positive and satisfy the triangle inequality `d(a, c) ≤ d(a, b) + d(b, c)`, and `0 < B`. -/
def WellFormed (i : TspInstance) : Prop :=
  Tsp.WellFormed i ∧
    (∀ a < i.1, ∀ b < i.1, a ≠ b → 0 < (i.2.1.getD a []).getD b 0) ∧
    (∀ a < i.1, ∀ b < i.1, ∀ c < i.1,
      (i.2.1.getD a []).getD c 0 ≤ (i.2.1.getD a []).getD b 0 + (i.2.1.getD b []).getD c 0) ∧
    0 < i.2.2

open Classical in
/-- METRIC TRAVELING SALESPERSON as a decision problem over bitstrings. -/
noncomputable def metricTravelingSalespersonDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := TspInstance) x with
  | some i => decide (WellFormed i ∧ TspFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.MetricTravelingSalesperson
