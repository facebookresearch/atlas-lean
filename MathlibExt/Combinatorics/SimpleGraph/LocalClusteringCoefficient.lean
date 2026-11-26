/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Combinatorics.SimpleGraph.Finite

/-! # Local clustering coefficient of a finite simple graph -/

namespace SimpleGraph

@[expose] public section

/-- **Local clustering coefficient.** For a vertex $v$ of a finite simple graph $G$, its local
clustering coefficient is the number of edges in the subgraph induced by the neighbors of $v$,
divided by $\binom{\deg_G(v)}{2}$, the number of unordered pairs of distinct neighbors. The
quotient is rational and is taken to be $0$ when $v$ has degree at most one.

Source: David Easley and Jon Kleinberg, *Networks, Crowds, and Markets*, Cambridge University
Press, 2010, Section 3.1 (triadic closure), with the value at degree at most one fixed by
convention. -/
def localClusteringCoefficient {V : Type*} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    (v : V) : ℚ :=
  ((G.induce (G.neighborSet v)).edgeFinset.card : ℚ) / (G.degree v).choose 2

end

end SimpleGraph
