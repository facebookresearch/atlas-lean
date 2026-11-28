/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# GENERALIZED SATISFIABILITY: definitions

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [LO6] GENERALIZED
SATISFIABILITY;
T. J. Schaefer, "The complexity of satisfiability problems", Proceedings of the
Tenth Annual ACM Symposium on Theory of Computing (STOC 1978), 216-226,
doi:10.1145/800133.804350.
-/
module

public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiability

/-- An instance: the number `n` of variables (variables `0, ..., n - 1`), and one triple
`(kᵢ, Rᵢ, Cᵢ)` per index `i`: the arity `kᵢ`, the relation `Rᵢ` as the list of its tuples, and
the collection `Cᵢ` of `kᵢ`-tuples of variables. -/
abbrev GeneralizedSatisfiabilityInstance := ℕ × List (ℕ × List (List Bool) × List (List ℕ))

/-- Well-formedness of an instance: every arity `kᵢ` is positive, every tuple of `Rᵢ` has length
`kᵢ`, and every tuple of `Cᵢ` has length `kᵢ` and consists of variables `< n`. -/
def WellFormed (i : GeneralizedSatisfiabilityInstance) : Prop :=
  ∀ c ∈ i.2, 0 < c.1 ∧ (∀ r ∈ c.2.1, r.length = c.1) ∧
    ∀ u ∈ c.2.2, u.length = c.1 ∧ ∀ x ∈ u, x < i.1

/-- A truth assignment `t` such that, for every index `i` and every tuple `u ∈ Cᵢ`, the tuple of
truth values `u.map t` belongs to `Rᵢ`. -/
def GeneralizedSatisfiabilityFeasible (i : GeneralizedSatisfiabilityInstance) : Prop :=
  ∃ t : ℕ → Bool, ∀ c ∈ i.2, ∀ u ∈ c.2.2, u.map t ∈ c.2.1

open Classical in
/-- GENERALIZED SATISFIABILITY as a decision problem over bitstrings. -/
noncomputable def generalizedSatisfiabilityDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := GeneralizedSatisfiabilityInstance) x with
  | some i => decide (WellFormed i ∧ GeneralizedSatisfiabilityFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.GeneralizedSatisfiability
