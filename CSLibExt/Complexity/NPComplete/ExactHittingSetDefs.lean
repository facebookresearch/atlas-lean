/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ExactHittingSet

/-- **An exact-hitting-set instance.** The number `r` of elements and a list of subsets of
`0, …, r - 1`, each given as a list (Karp 1972, problem 15). -/
abbrev ExactHittingSetInstance := ℕ × List (List ℕ)

/-- **Well-formed exact-hitting-set instances.** Every listed subset has no repeated entry and only
entries below `r`. -/
def WellFormed (i : ExactHittingSetInstance) : Prop :=
  ∀ s ∈ i.2, s.Nodup ∧ ∀ x ∈ s, x < i.1

/-- **Feasible exact-hitting-set instances.** Some set `W` of elements below `r` meets every
listed subset in exactly one element (Karp 1972, problem 15). -/
def ExactHittingSetFeasible (i : ExactHittingSetInstance) : Prop :=
  ∃ W : Finset ℕ, (∀ x ∈ W, x < i.1) ∧ ∀ s ∈ i.2, (s.filter (· ∈ W)).length = 1

open Classical in
/-- **The exact HITTING SET decision problem.** It accepts a bitstring exactly when it decodes to a
well-formed, feasible exact-hitting-set instance. -/
noncomputable def exactHittingSetDec : MetaMathlibExt.ComplexityTheory.DecisionProblem :=
  fun x =>
    match MetaMathlibExt.BitstringEncoding.bitDecode (α := ExactHittingSetInstance) x with
    | some i => decide (WellFormed i ∧ ExactHittingSetFeasible i)
    | none => false

end MetaMathlibExt.Complexity.NPComplete.ExactHittingSet
