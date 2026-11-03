/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Markov-equivalent DAGs are connected by covered-edge reversals

Sources:
T. Verma and J. Pearl, "Equivalence and synthesis of causal models", *Proc. 6th Conference on
Uncertainty in Artificial Intelligence* (1990); D. M. Chickering, "A transformational
characterization of equivalent Bayesian network structures", *Proc. 11th Conference on
Uncertainty in Artificial Intelligence* (1995); arXiv:1302.4938.
-/
module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.GraphicalModels.BayesianDirichletScore

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels.BayesianDirichlet

/-!
# Markov-equivalent DAGs are connected by covered-edge reversals

A structure is a parent-set map `Pa : V → Finset V` (edge `u → v` iff `u ∈ Pa v`). By Verma and
Pearl, two DAGs are Markov equivalent iff they have the same skeleton and the same
v-structures. Chickering's theorem says that then one is reachable from the other by a sequence
of covered-edge reversals (`CoveredReversal`, proved to preserve the BDe score in
`CSLibExt/MachineLearning/GraphicalModels/BayesianDirichletScore.lean`); with
`bdeScore_eq_of_reflTransGen` this gives the score equivalence of BDe (Heckerman, Geiger and
Chickering 1995).
-/

variable {V : Type*}

/-- The structure has no directed cycle. -/
def IsAcyclic (Pa : V → Finset V) : Prop :=
  ∀ v, ¬Relation.TransGen (fun u w => u ∈ Pa w) v v

/-- `u` and `w` are adjacent (joined by an edge in either direction). -/
def Adjacent (Pa : V → Finset V) (u w : V) : Prop := u ∈ Pa w ∨ w ∈ Pa u

/-- `u → w ← z` is a v-structure: two non-adjacent distinct parents of a common child. -/
def IsVStructure (Pa : V → Finset V) (u w z : V) : Prop :=
  u ≠ z ∧ u ∈ Pa w ∧ z ∈ Pa w ∧ ¬Adjacent Pa u z

/-- **Chickering's transformational characterization** (1995): two acyclic structures with the
same skeleton and the same v-structures (Markov equivalent by Verma and Pearl) are connected by
a sequence of covered-edge reversals. -/
public theorem_wanted reflTransGen_coveredReversal_of_markovEquivalent [DecidableEq V]
    [Finite V]
    {Pa Pa' : V → Finset V} (h : IsAcyclic Pa) (h' : IsAcyclic Pa')
    (hskel : ∀ u w, Adjacent Pa u w ↔ Adjacent Pa' u w)
    (hv : ∀ u w z, IsVStructure Pa u w z ↔ IsVStructure Pa' u w z) :
    Relation.ReflTransGen CoveredReversal Pa Pa'

end Cslib.MachineLearning.GraphicalModels.BayesianDirichlet
