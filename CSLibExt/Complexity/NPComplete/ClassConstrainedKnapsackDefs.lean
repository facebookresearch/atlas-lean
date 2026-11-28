/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# CLASS-CONSTRAINED KNAPSACK: definitions

Source:
P. Crescenzi and V. Kann (eds.), *A compendium of NP optimization problems* (web edition,
2000), problem MAXIMUM CLASS-CONSTRAINED KNAPSACK;
H. Shachnai and T. Tamir, "On two class-constrained versions of the multiple knapsack
problem", Algorithmica 29 (2001), 442-467, doi:10.1007/s004530010057 (the class-constrained
multiple knapsack problem, CMKP, is NP-hard).
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.ClassConstrainedKnapsack

/-- An instance: the set sizes `[U₀, ..., U_{n-1}]`, the knapsacks as pairs
`(volume Vⱼ, compartments Cⱼ)`, and the bound `K`. -/
abbrev ClassConstrainedKnapsackInstance := List ℕ × List (ℕ × ℕ) × ℕ

/-- Well-formedness of an instance: `∑ᵢ Uᵢ = ∑ⱼ Vⱼ` and `0 < K`. -/
def WellFormed (i : ClassConstrainedKnapsackInstance) : Prop :=
  i.1.sum = (i.2.1.map Prod.fst).sum ∧ 0 < i.2.2

/-- Some placement `(I, Q)` respects every volume, compartment and set-size bound, uses only
allotted compartments, and packs at least `K` elements. -/
def ClassConstrainedKnapsackFeasible (i : ClassConstrainedKnapsackInstance) : Prop :=
  ∃ I : Fin i.1.length → Fin i.2.1.length → Bool,
    ∃ Q : Fin i.1.length → Fin i.2.1.length → ℕ,
      (∀ j, ∑ k, Q k j ≤ i.2.1[j].1) ∧
      (∀ j, ∑ k, (I k j).toNat ≤ i.2.1[j].2) ∧
      (∀ k, ∑ j, Q k j ≤ i.1[k]) ∧
      (∀ k j, I k j = false → Q k j = 0) ∧
      i.2.2 ≤ ∑ k, ∑ j, Q k j

open Classical in
/-- CLASS-CONSTRAINED KNAPSACK as a decision problem over bitstrings. -/
noncomputable def classConstrainedKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := ClassConstrainedKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ ClassConstrainedKnapsackFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.ClassConstrainedKnapsack
