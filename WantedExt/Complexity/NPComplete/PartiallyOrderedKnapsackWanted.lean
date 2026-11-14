/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# PARTIALLY ORDERED KNAPSACK is NP-complete

Source:
M. R. Garey and D. S. Johnson, *Computers and Intractability: A Guide to the
Theory of NP-Completeness*, W. H. Freeman (1979), problem [MP12] PARTIALLY
ORDERED KNAPSACK;
D. S. Johnson and K. A. Niemi, "On knapsacks, partitions, and a new dynamic
programming technique for trees", Mathematics of Operations Research 8 (1983),
1-14, doi:10.1287/moor.8.1.1.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.Computability.CookLevin
public import MathlibExt.Computability.BinaryNatEncoding
public import MathlibExt.Computability.Complexity
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Order.Defs.Unbundled

@[expose] public section

namespace MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsack

/-!
# PARTIALLY ORDERED KNAPSACK is NP-complete

INSTANCE: a finite set `U`, a partial order `<` on `U`, for each `u ∈ U` a size `s(u) ∈ ℤ⁺` and a
value `v(u) ∈ ℤ⁺`, and positive integers `B` and `K`. QUESTION: is there a subset `U' ⊆ U` such
that if `u ∈ U'` and `u' < u`, then `u' ∈ U'`, and such that `∑_{u ∈ U'} s(u) ≤ B` and
`∑_{u ∈ U'} v(u) ≥ K`?

The elements are `Fin n`, `n` the length of the list of (size, value) pairs. The order is given
as the list of its pairs `(a, b)`, meaning `uₐ < u_b`; `WellFormed` requires the relation it
lists to be a strict partial order, Mathlib's `IsStrictOrder` (irreflexive and transitive).

Encoding: the instance is decoded from a bitstring with the repository's
canonical `MetaMathlibExt.BitstringEncoding`. Undecodable bitstrings, and
bitstrings decoding to malformed instances, are no-instances.

NP-completeness is stated in the same form as the proved results in
`CSLibExt.Computability.Complexity.Karp`: membership in
`MetaMathlibExt.ComplexityTheory.NP`, plus a polynomial-time many-one
reduction from every language in `NP`
(`Cslib.CookLevin.PolyManyOneRed`).
-/

/-- An instance: the (size, value) pairs of the elements `u₀, …, u_{n-1}`, the pairs `(a, b)`
with `uₐ < u_b`, and the bounds `B` and `K`. -/
abbrev PartiallyOrderedKnapsackInstance := List (ℕ × ℕ) × List (ℕ × ℕ) × ℕ × ℕ

/-- The order of the instance as a relation on `Fin n`. -/
def Precedes (i : PartiallyOrderedKnapsackInstance) (a b : Fin i.1.length) : Prop :=
  ((a : ℕ), (b : ℕ)) ∈ i.2.1

/-- The size of an element. -/
def size (i : PartiallyOrderedKnapsackInstance) (u : Fin i.1.length) : ℕ := (i.1.get u).1

/-- The value of an element. -/
def value (i : PartiallyOrderedKnapsackInstance) (u : Fin i.1.length) : ℕ := (i.1.get u).2

/-- Well-formedness of an instance: the order pairs name elements, the relation they list is a
strict partial order, every size and value is positive, and `B` and `K` are positive. -/
def WellFormed (i : PartiallyOrderedKnapsackInstance) : Prop :=
  (∀ p ∈ i.2.1, p.1 < i.1.length ∧ p.2 < i.1.length) ∧ IsStrictOrder (Fin i.1.length) (Precedes i) ∧
    (∀ u ∈ i.1, 0 < u.1 ∧ 0 < u.2) ∧ 0 < i.2.2.1 ∧ 0 < i.2.2.2

/-- Some subset `U'`, closed under predecessors, has total size at most `B` and total value at
least `K`. -/
def PartiallyOrderedKnapsackFeasible (i : PartiallyOrderedKnapsackInstance) : Prop :=
  ∃ S : Finset (Fin i.1.length), (∀ u ∈ S, ∀ u', Precedes i u' u → u' ∈ S) ∧
    ∑ u ∈ S, size i u ≤ i.2.2.1 ∧ i.2.2.2 ≤ ∑ u ∈ S, value i u

open Classical in
/-- PARTIALLY ORDERED KNAPSACK as a decision problem over bitstrings. -/
noncomputable def partiallyOrderedKnapsackDec :
    MetaMathlibExt.ComplexityTheory.DecisionProblem := fun x =>
  match MetaMathlibExt.BitstringEncoding.bitDecode
      (α := PartiallyOrderedKnapsackInstance) x with
  | some i => decide (WellFormed i ∧ PartiallyOrderedKnapsackFeasible i)
  | none => false

/-- **PARTIALLY ORDERED KNAPSACK is NP-complete.** Source: Garey and Johnson (1979), [MP12];
Johnson and Niemi (1983). -/
public theorem_wanted partiallyOrderedKnapsack_npComplete :
    partiallyOrderedKnapsackDec ∈ MetaMathlibExt.ComplexityTheory.NP ∧
      ∀ L : MetaMathlibExt.ComplexityTheory.DecisionProblem,
        L ∈ MetaMathlibExt.ComplexityTheory.NP →
          Cslib.CookLevin.PolyManyOneRed L partiallyOrderedKnapsackDec

end MetaMathlibExt.Complexity.NPComplete.PartiallyOrderedKnapsack
