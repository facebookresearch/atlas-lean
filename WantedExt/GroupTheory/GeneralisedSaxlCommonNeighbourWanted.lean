/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Generalised Saxl Common Neighbour Conjecture.
Source record `OWR-14299292-003` (UnsolvedMath id 30006342).
Freedman, Huang, Lee and Rekvényi, arXiv:2410.22613v4 (28 January 2026),
Definition 1.1 and Conjecture 1.2, pages 1-2, where it is stated as open. Resolved false:
Rizzoli and Thomas, arXiv:2609.01367 (Kourovka Notebook, 21st issue, Problem 21.29).
-/
module

public import Mathlib.Data.Fintype.Perm
public import Mathlib.GroupTheory.GroupAction.FixingSubgroup
public import Mathlib.GroupTheory.GroupAction.Primitive
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Batteries.Util.ProofWanted

@[expose] public section

namespace MathlibExt.GroupTheory.GeneralisedSaxlCommonNeighbourWanted

/-- A base of minimum cardinality, with trivial canonical pointwise stabilizer. -/
def IsMinimumBase {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) (B : Finset Ω) : Prop :=
  fixingSubgroup G (B : Set Ω) = ⊥ ∧
    ∀ C : Finset Ω, fixingSubgroup G (C : Set Ω) = ⊥ → B.card ≤ C.card

/-- Distinct points are adjacent precisely when they extend to a minimum-size base. -/
def generalisedSaxlGraph {Ω : Type*}
    (G : Subgroup (Equiv.Perm Ω)) : SimpleGraph Ω where
  Adj α β := α ≠ β ∧ ∃ B : Finset Ω, IsMinimumBase G B ∧ α ∈ B ∧ β ∈ B
  symm := ⟨fun _α _β ⟨h, B, hB, hα, hβ⟩ => ⟨h.symm, B, hB, hβ, hα⟩⟩
  loopless := ⟨fun _α h => h.1 rfl⟩

/-- Conjecture 1.2: every pair has a common neighbour for finite primitive
permutation groups whose minimum base cardinality is at least two. -/
def conjecture : Prop :=
  ∀ (Ω : Type) [Fintype Ω] [Nontrivial Ω]
    (G : Subgroup (Equiv.Perm Ω)),
    MulAction.IsPreprimitive G Ω →
    (∀ B : Finset Ω, fixingSubgroup G (B : Set Ω) = ⊥ → 2 ≤ B.card) →
    ∀ α β : Ω, ((generalisedSaxlGraph G).commonNeighbors α β).Nonempty

-- Carried source audit `OWR-14299292-003` (see the Moved/ record).

/--
Resolved false: Resolved false. Rizzoli and Thomas (Common neighbour conjectures for Saxl graphs
fail at every base size, arXiv:2609.01367, 2026) construct, for every B >= 2, infinitely many
primitive groups of base size B whose generalised Saxl graphs have two non-adjacent vertices
without a common neighbour; the base-two case is the Burness-Giudici conjecture, and the
Kourovka Notebook (No. 21, Problem 21.29) records it as answered: "No, not always". Source: A.
Rizzoli, A. R. Thomas, Common neighbour conjectures for Saxl graphs fail at every base size,
arXiv:2609.01367 (2026), https://arxiv.org/abs/2609.01367; E. I. Khukhro and V. D. Mazurov
(eds.), Unsolved Problems in Group Theory: The Kourovka Notebook, 21st issue, arXiv:1401.0300v49
(20 October 2026), Problem 21.29, https://arxiv.org/abs/1401.0300v49. Moved from
`OpenConjectures/GroupTheory/GeneralisedSaxlCommonNeighbour`.
-/
public theorem_wanted conjecture_refuted : ¬ conjecture

end MathlibExt.GroupTheory.GeneralisedSaxlCommonNeighbourWanted
