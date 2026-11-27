/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Set.Card

@[expose] public section

/-!
# Unique subgraphs

Ported from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/SubgraphIsomorphism.lean`
in google-deepmind/formal-conjectures (needed by the `ErdosProblem426` entry).
-/

namespace SimpleGraph

variable {V : Type*}

/-- **Unique subgraph.** Let $G$ and $H$ be graphs on the same vertex set $V$. Then $G$ is a
unique subgraph of $H$ if exactly one subgraph of $H$ is isomorphic to $G$. Here a subgraph of
$H$ means a spanning subgraph: a graph on $V$ all of whose edges are edges of $H$ (not
necessarily induced). -/
def IsUniqueSubgraph (G H : SimpleGraph V) : Prop :=
  ∃! G' : SimpleGraph V, G' ≤ H ∧ Nonempty (G.Iso G')

/-- **Number of unique subgraphs.** Let $H$ be a graph on a finite vertex set $V$. The number of
unique subgraphs of $H$ is the number of spanning subgraphs $G$ of $H$ (graphs on $V$ all of
whose edges are edges of $H$) that are unique subgraphs of $H$, that is, isomorphic to no other
spanning subgraph of $H$.

Equivalently, it is the number of isomorphism classes of graphs on $V$ that occur exactly once
as a spanning subgraph of $H$: sending each such $G$ to its isomorphism class is a bijection onto
these classes. In particular, isomorphic copies do not inflate the count: if two distinct
spanning subgraphs of $H$ are isomorphic, neither is a unique subgraph of $H$, so neither is
counted. -/
noncomputable def uniqueSubgraphCount [Finite V] (H : SimpleGraph V) : ℕ :=
  {G : SimpleGraph V | G ≤ H ∧ IsUniqueSubgraph G H}.ncard

end SimpleGraph
