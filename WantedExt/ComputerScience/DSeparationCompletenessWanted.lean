/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Batteries.Util.ProofWanted
public import CSLibExt.MachineLearning.GraphicalModels.GlobalMarkov

/-!
# Completeness of d-separation

The global Markov property (`BayesNet.condIndep_of_dSeparated` in
`CSLibExt/MachineLearning/GraphicalModels/GlobalMarkov.lean`) says that d-separation in the
graph of a Bayesian network implies conditional independence under its joint law. The converse
direction, completeness, says that d-separation is the strongest such graphical test: every
triple that is not d-separated is conditionally dependent under some network on the same graph.

## References

* J. Pearl, *Causal diagrams for empirical research*, Biometrika 82(4) (1995), 669–710, §2.1.
* D. Geiger, T. Verma and J. Pearl, *Identifying independence in Bayesian networks*, Networks
  20(5) (1990), 507–534.
* C. Meek, *Strong completeness and faithfulness in Bayesian networks*, Proc. 11th Conference on
  Uncertainty in Artificial Intelligence (1995); arXiv:1302.4973, §2.
-/

@[expose] public section

namespace Cslib.MachineLearning.GraphicalModels

open MetaMathlibExt.FiniteWeight

namespace BayesNet

variable {n : ℕ}

/-- **Completeness of d-separation** (Geiger, Verma and Pearl 1990; Pearl 1995, §2.1: the
conditional independencies implied by the factorization over a DAG are exactly the
d-separations; Meek 1995, Theorem 1 and footnote 1, for a fixed discrete state space): if
pairwise disjoint sets `X, Y, Z` of nodes are not d-separated in the graph of `b`, then some
Bayesian network on the same graph and the same finite state space, with at least two states,
makes `X` and `Y` conditionally dependent given `Z`. -/
theorem_wanted exists_not_condIndep_of_not_dSeparated {α : Type*} [Fintype α] [Nontrivial α]
    (b : BayesNet α n) (X Y Z : Finset (Fin n)) (hXY : Disjoint X Y) (hXZ : Disjoint X Z)
    (hYZ : Disjoint Y Z) (h : ¬b.DSeparated ↑X ↑Y ↑Z) :
    ∃ b' : BayesNet α n, b'.pa = b.pa ∧ ¬CondIndep b'.joint ↑X ↑Y ↑Z

end BayesNet

end Cslib.MachineLearning.GraphicalModels
