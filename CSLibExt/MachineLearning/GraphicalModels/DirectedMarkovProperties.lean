/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import CSLibExt.MachineLearning.GraphicalModels.MarkovFactorization
import Mathlib.Tactic.TFAE

/-!
# The directed Markov properties are equivalent

For a directed acyclic graph (the graph of a Bayesian network `b`, nodes in a topological
order; its tables play no role) and any law `P` on `Fin n → α` with `α` finite, the following
are equivalent (Lauritzen, *Markov properties for directed graphs*, 2009: `(G) ⇔ (L) ⇔ (O)`, and
`(F) ⇔ (G)`):

* (F) `P` factorizes over the graph: it is the joint law of a Bayesian network on the same
  parent sets;
* (G) the global Markov property: d-separation implies conditional independence under `P`;
* (L) the local Markov property: every node is independent of its non-descendants that are not
  parents, given its parents;
* (O) the ordered Markov property (`OrderedMarkov`).

No positivity assumption is needed, in contrast with the undirected Hammersley–Clifford theorem.

## Main definitions

* `GlobalMarkovFor P b`, `LocalMarkovFor P b`: the global and local Markov properties of `P` for
  the graph of `b`.

## Main results

* `globalMarkovFor_of_factorizes`, `localMarkovFor_of_globalMarkovFor`,
  `orderedMarkov_of_localMarkovFor` and `exists_bayesNet_of_orderedMarkov`: the cycle
  `(F) ⇒ (G) ⇒ (L) ⇒ (O) ⇒ (F)`. The step (G) ⇒ (L) uses
  `BayesNet.dSeparated_localMarkov` (the parents of a node d-separate it from its other
  non-descendants), from `CSLibExt.MachineLearning.GraphicalModels.MarkovBlanket`.
* `directedMarkov_tfae`: the four properties are equivalent.

## References

* S. L. Lauritzen, *Markov properties for directed graphs*, Graphical Models lecture notes,
  University of Oxford (2009).
* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–710, §2.1.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open Finset Convexity MetaMathlibExt.FiniteWeight

variable {α : Type*} {n : ℕ}

/-- **The global Markov property for a graph** (Lauritzen 2009, property (G)): every
d-separation in the graph of `b` is a conditional independence of `P`. Like `CondIndep`, it is
defined for an arbitrary weight function `P`; it is the property of a law when `P` is
nonnegative with total mass `1`, as in `directedMarkov_tfae`. For the zero weight it holds for
every graph. -/
def GlobalMarkovFor [Fintype α] (P : (Fin n → α) → ℝ) (b : BayesNet α n) : Prop :=
  ∀ X Y Z : Set (Fin n), b.DSeparated X Y Z → CondIndep P X Y Z

/-- **The local Markov property for a graph** (Lauritzen 2009, property (L)): under `P`, every
node is conditionally independent of its non-descendants that are not its parents, given its
parents, in the graph of `b`. Like `CondIndep`, it is defined for an arbitrary weight function
`P`; it is the property of a law when `P` is nonnegative with total mass `1`, as in
`directedMarkov_tfae`. For the zero weight it holds for every graph. -/
def LocalMarkovFor [Fintype α] (P : (Fin n → α) → ℝ) (b : BayesNet α n) : Prop :=
  ∀ k, CondIndep P {k} {j | ¬b.IsDescendant k j ∧ ¬b.Edge j k} {j | b.Edge j k}

/-- **Factorization implies the global Markov property** ((F) ⇒ (G)). The joint law of a network
on the parent sets of `b` has the global Markov property for the graph of `b`. -/
theorem globalMarkovFor_of_factorizes [Fintype α] [Nonempty α] {b b' : BayesNet α n}
    (h : b'.pa = b.pa) : GlobalMarkovFor b'.joint b := by
  intro X Y Z hd
  apply b'.condIndep_of_dSeparated
  obtain ⟨pa, cpt⟩ := b
  obtain ⟨pa', cpt'⟩ := b'
  simp only at h
  subst h
  exact hd

/-- **The global Markov property implies the local one** ((G) ⇒ (L)). -/
theorem localMarkovFor_of_globalMarkovFor [Fintype α] {P : (Fin n → α) → ℝ} {b : BayesNet α n}
    (h : GlobalMarkovFor P b) : LocalMarkovFor P b :=
  fun k => h _ _ _ (b.dSeparated_localMarkov k)

/-- **The local Markov property implies the ordered one** ((L) ⇒ (O)), by decomposition: the
predecessors of `k` are non-descendants of `k`. -/
theorem orderedMarkov_of_localMarkovFor [Fintype α] {P : (Fin n → α) → ℝ} {b : BayesNet α n}
    (h : LocalMarkovFor P b) : OrderedMarkov P b.pa := by
  classical
  intro k
  have hl := h k
  set B := univ.filter fun j => ¬b.IsDescendant k j ∧ ¬b.Edge j k
  have eK : ({k} : Set (Fin n)) = ↑({k} : Finset (Fin n)) := by simp
  have eB : {j | ¬b.IsDescendant k j ∧ ¬b.Edge j k} = (↑B : Set (Fin n)) := by ext j; simp [B]
  have ePa : {j | b.Edge j k} = (↑(parentSet b.pa k) : Set (Fin n)) := by
    ext j
    simp only [Set.mem_ofPred_eq, mem_coe, mem_parentSet]
    rfl
  rw [eK, eB, ePa] at hl
  have hsub : nonParentPred b.pa k ⊆ B := by
    intro j hj
    simp only [nonParentPred, mem_filter, mem_univ, true_and] at hj
    simp only [B, mem_filter, mem_univ, true_and]
    exact ⟨fun hd => absurd hd.le (not_le.2 hj.1), fun he => hj.2 (mem_parentSet.2 he)⟩
  have hdisj : Disjoint B {k} := by
    rw [disjoint_singleton_right]
    intro hk
    simp only [B, mem_filter, mem_univ, true_and] at hk
    exact hk.1 .refl
  exact condIndep_symm (condIndep_mono_left (condIndep_symm hl) hsub hdisj)

/-- **The directed Markov properties are equivalent** (Lauritzen 2009): for a law `P` on
`Fin n → α` and the graph of a Bayesian network `b`, factorization over the graph, the global,
the local and the ordered Markov properties are equivalent. -/
theorem directedMarkov_tfae [Fintype α] [Nonempty α] (P : (Fin n → α) → ℝ) (hP : ∀ x, 0 ≤ P x)
    (h1 : ∑ x, P x = 1) (b : BayesNet α n) :
    [∃ b' : BayesNet α n, b'.pa = b.pa ∧ b'.joint = P, GlobalMarkovFor P b, LocalMarkovFor P b,
      OrderedMarkov P b.pa].TFAE := by
  tfae_have 1 → 2 := by
    rintro ⟨b', hpa, rfl⟩
    exact globalMarkovFor_of_factorizes hpa
  tfae_have 2 → 3 := localMarkovFor_of_globalMarkovFor
  tfae_have 3 → 4 := orderedMarkov_of_localMarkovFor
  tfae_have 4 → 1 := exists_bayesNet_of_orderedMarkov P hP h1 b.pa
  tfae_finish

end Cslib.MachineLearning.GraphicalModels
