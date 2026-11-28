/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEASIBLE REGISTER ASSIGNMENT: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 272, problem [PO2]
FEASIBLE REGISTER ASSIGNMENT;
R. Sethi, "Complete register allocation problems", SIAM Journal on Computing 4
(1975), 226-248, doi:10.1137/0204020.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.RegisterSufficiencyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeasibleRegisterAssignment

open MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency

/-- An instance: the vertex count `n`, the arc list `A`, the bound `K`, and the register
assignment as the list `[f 0, ..., f (n - 1)]` of register indices. -/
abbrev FeasibleRegisterAssignmentInstance := ℕ × List (ℕ × ℕ) × ℕ × List ℕ

/-- The underlying REGISTER SUFFICIENCY instance `(n, A, K)`. -/
def toRegisterSufficiency (i : FeasibleRegisterAssignmentInstance) :
    RegisterSufficiencyInstance :=
  (i.1, i.2.1, i.2.2.1)

/-- Well-formedness of an instance: `(n, A, K)` is a well-formed REGISTER SUFFICIENCY instance
(a directed acyclic graph and `K ≥ 1`), and the assignment gives each of the `n` vertices a
register index below `K`. -/
def WellFormed (i : FeasibleRegisterAssignmentInstance) : Prop :=
  RegisterSufficiency.WellFormed (toRegisterSufficiency i) ∧ i.2.2.2.length = i.1 ∧
    ∀ r ∈ i.2.2.2, r < i.2.2.1

/-- A computation for `G` (all the properties of REGISTER SUFFICIENCY, for the bound `K`) in
which no `Sᵢ`, `1 ≤ i ≤ n`, holds two vertices assigned the same register. -/
def FeasibleRegisterAssignmentFeasible (i : FeasibleRegisterAssignmentInstance) : Prop :=
  ∃ v : Equiv.Perm (Fin i.1), ∃ S : Fin (i.1 + 1) → Finset (Fin i.1),
    (∀ k, (S k).card ≤ i.2.2.1) ∧ S 0 = ∅ ∧
      (∀ u, (∀ w, ¬ (Graph (toRegisterSufficiency i)).Adj w u) → u ∈ S (Fin.last i.1)) ∧
      (∀ k : Fin i.1, v k ∈ S k.succ ∧ S k.succ \ {v k} ⊆ S k.castSucc ∧
        ∀ u, (Graph (toRegisterSufficiency i)).Adj (v k) u → u ∈ S k.castSucc) ∧
      ∀ k : Fin (i.1 + 1), 0 < (k : ℕ) → ∀ u ∈ S k, ∀ w ∈ S k,
        i.2.2.2.getD u 0 = i.2.2.2.getD w 0 → u = w

open Classical in
/-- FEASIBLE REGISTER ASSIGNMENT as a decision problem over bitstrings. -/
noncomputable def feasibleRegisterAssignmentDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := FeasibleRegisterAssignmentInstance) x with
  | some i => decide (WellFormed i ∧ FeasibleRegisterAssignmentFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.FeasibleRegisterAssignment
