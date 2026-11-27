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

public import Mathlib.Combinatorics.SimpleGraph.Clique

@[expose] public section

/-!
# Independence number of a neighbourhood

Ported from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Independence.lean`
in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(the `indepNeighborsCard` fragment only). The definition is unchanged; the
unrelated declarations of the source file are not ported.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- For a graph on a finite vertex type, the independence number of the subgraph induced on
the neighbourhood of `v`: the largest size of a set of pairwise non-adjacent neighbours of
`v` (Mathlib's `indepNum`, the supremum in `ℕ` of the sizes of independent finsets). -/
noncomputable def indepNeighborsCard (G : SimpleGraph α) (v : α) : ℕ :=
  (G.induce (G.neighborSet v)).indepNum

end SimpleGraph
