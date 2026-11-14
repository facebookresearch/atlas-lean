/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# FEASIBLE REGISTER ASSIGNMENT is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), p. 272, problem [PO2]
FEASIBLE REGISTER ASSIGNMENT;
R. Sethi, "Complete register allocation problems", SIAM Journal on Computing 4
(1975), 226-248, doi:10.1137/0204020.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import WantedExt.Complexity.NPComplete.RegisterSufficiencyWanted

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.FeasibleRegisterAssignment

open MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency

/-!
# FEASIBLE REGISTER ASSIGNMENT is NP-complete

INSTANCE: a directed acyclic graph `G = (V, A)`, a positive integer `K`, and a register
assignment `f : V → {R₁, R₂, ..., R_K}`. QUESTION: is there a computation for `G` using the
given register assignment, i.e., an ordering `v₁, v₂, ..., vₙ` of `V` and a sequence
`S₀, S₁, ..., Sₙ` of subsets of `V` that satisfies all the properties given in REGISTER
SUFFICIENCY and that in addition satisfies, for `1 ≤ j ≤ K` and `1 ≤ i ≤ n`, there is at most
one vertex `u ∈ Sᵢ` for which `f(u) = R_j`?

The digraph, its well-formedness and the properties of a computation are those of
`MetaMathlibExt.Complexity.NPComplete.RegisterSufficiency` ([PO1]): an arc `(v, u)` says that
`u` is an operand of `v`; the ordering is a permutation `v` of `Fin n`; `S k` is `Sₖ`;
`|Sᵢ| ≤ K`, `S₀ = ∅`, `Sₙ` contains every vertex of in-degree `0`, and for each step
`vᵢ ∈ Sᵢ`, `Sᵢ - {vᵢ} ⊆ Sᵢ₋₁`, and `Sᵢ₋₁` contains every operand of `vᵢ`. The register
assignment is a list giving, for each vertex `u`, the index `f u < K` of its register
(`R_{f u + 1}`).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

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

/-- **FEASIBLE REGISTER ASSIGNMENT is NP-complete.** Source: Garey and Johnson (1979), [PO2];
Sethi (1975). -/
public theorem_wanted feasibleRegisterAssignment_npComplete :
    feasibleRegisterAssignmentDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L feasibleRegisterAssignmentDec

end MetaMathlibExt.Complexity.NPComplete.FeasibleRegisterAssignment
