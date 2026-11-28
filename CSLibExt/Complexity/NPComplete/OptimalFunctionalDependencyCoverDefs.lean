/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# OPTIMAL COVER OF FUNCTIONAL DEPENDENCIES: definitions

Source:
D. Maier, "Minimum covers in the relational database model", Journal of the ACM 27 (1980),
664-674, doi:10.1145/322217.322223;
D. Maier, *The Theory of Relational Databases*, Computer Science Press (1983), Chapter 5,
Definition 5.1 and Section 5.7 (optimal covers; finding one is NP-complete).
-/
module

public import CSLibExt.Databases.FunctionalDependencies
public import CSLibExt.Databases.NormalForms
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import CSLibExt.Complexity.NPComplete.MinimumCardinalityKeyDefs

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.OptimalFunctionalDependencyCover

/-- An instance: the number of attributes `a` (attributes `0, ..., a - 1`), the functional
dependencies (pairs of attribute lists `(X, Y)` for `X → Y`), and the bound `K`. -/
abbrev OptimalFunctionalDependencyCoverInstance := ℕ × List (List ℕ × List ℕ) × ℕ

/-- Well-formedness of an instance: every dependency mentions only attributes of `U`. -/
def WellFormed (i : OptimalFunctionalDependencyCoverInstance) : Prop :=
  ∀ f ∈ i.2.1, (∀ x ∈ f.1, x < i.1) ∧ ∀ x ∈ f.2, x < i.1

/-- The size of a set of functional dependencies: its number of attribute symbols. -/
def size {A : Type*} (G : Finset (Cslib.Databases.FD A)) : ℕ :=
  ∑ g ∈ G, (g.lhs.card + g.rhs.card)

/-- Some set `G` of functional dependencies over `U`, equivalent to `F` and of size at most
`K`. -/
def OptimalFunctionalDependencyCoverFeasible
    (i : OptimalFunctionalDependencyCoverInstance) : Prop :=
  ∃ G : Finset (Cslib.Databases.FD (Fin i.1)),
    Cslib.Databases.Equivalent (MinimumCardinalityKey.deps i) G ∧ size G ≤ i.2.2

open Classical in
/-- OPTIMAL COVER OF FUNCTIONAL DEPENDENCIES as a decision problem over bitstrings. -/
noncomputable def optimalFunctionalDependencyCoverDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := OptimalFunctionalDependencyCoverInstance) x with
  | some i => decide (WellFormed i ∧ OptimalFunctionalDependencyCoverFeasible i)
  | none => false

end MetaMathlibExt.Complexity.NPComplete.OptimalFunctionalDependencyCover
