/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
Author: Stefan Trandafir
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Combinatorics.SimpleGraph.LineGraph

@[expose] public section

-- Source: Lean Definition Library (Airtable) records: Combinatorics 428

/-!
# LineGraph

Definitions from the AAI Lean Definition Library (Knowledge Expert Program).
Source records: Combinatorics 428

## References

* Algebraic Graph Theory, Godsil & Royle (2001), Section 1.7 Line graphs, page 10. (for
  `SimpleGraph.IsLineGraph`)
-/

namespace MetaMathlibExt

-- Combinatorics 428: Is line graph

/-- **Graphs that are line graphs.** A simple graph $G$ on a finite vertex type is a line graph if
there are a natural number $k$ and a simple graph $H$ on the vertex set $\{0, \dots, k-1\}$ such
that $G$ is isomorphic to the line graph $L(H)$. Here $L(H)$ has the edges of $H$ as its vertices,
and two distinct edges of $H$ are adjacent in $L(H)$ when they share an endpoint.
-/
def SimpleGraph.IsLineGraph {V : Type*} [Fintype V] (G : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (H : SimpleGraph (Fin k)),
    Nonempty (G ≃g H.lineGraph)

end MetaMathlibExt

end
