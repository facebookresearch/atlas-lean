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

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
# Well totally dominated graphs

A *total dominating set* of `G` is a set `S` of vertices such that every vertex
of `G` (including the vertices of `S`) has a neighbour in `S`. A total
dominating set `S` is *minimal* if no proper subset of `S` is also a total
dominating set. A graph `G` is *well totally dominated* if every minimal total
dominating set has the same cardinality.

Ported from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/WellTotallyDominated.lean`
in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(the three definitions below only; the `pendantVertices` definition of the
source file is not ported). The definitions are unchanged.

Note that `SimpleGraph.IsDominating` in
`MathlibExt.Combinatorics.SimpleGraph.Domination` is the *ordinary* domination
predicate, which only requires every vertex outside `S` to have a neighbour in
`S`; total domination is a strictly stronger requirement, so the two are
genuinely different notions rather than duplicates.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- For a graph `G` on a finite vertex type, a finite set `S` of vertices is a total
dominating set if every vertex, including each vertex of `S`, has a neighbor in `S`. -/
def IsTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  ∀ v : α, ∃ w ∈ S, G.Adj v w

/-- For a graph on a finite vertex type, a total dominating set `S` is minimal if no proper
subset of `S` is also a total dominating set. -/
def IsMinimalTotalDominatingSet (G : SimpleGraph α) [DecidableRel G.Adj] (S : Finset α) : Prop :=
  IsTotalDominatingSet G S ∧
  ∀ T : Finset α, T ⊂ S → ¬IsTotalDominatingSet G T

/-- A graph `G` on a finite vertex type is well totally dominated if any two minimal total
dominating sets have the same cardinality. This holds vacuously when `G` has no total
dominating set, for example when it has an isolated vertex. -/
def IsWellTotallyDominated (G : SimpleGraph α) [DecidableRel G.Adj] : Prop :=
  ∀ S T : Finset α,
    IsMinimalTotalDominatingSet G S →
    IsMinimalTotalDominatingSet G T →
    S.card = T.card

end SimpleGraph
