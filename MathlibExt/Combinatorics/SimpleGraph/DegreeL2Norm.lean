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

public import Mathlib.Analysis.Real.Sqrt
public import Mathlib.Combinatorics.SimpleGraph.Finite

@[expose] public section

/-!
# The length of a graph: the Euclidean norm of its degree sequence

Ported from `FormalConjecturesForMathlib/Combinatorics/SimpleGraph/Degrees.lean`
in [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures)
(the `degreeL2Norm` fragment only). The definition is unchanged; the unrelated
declarations of the source file are not ported.

This quantity is written `length(G)` in E. DeLaVina's *Written on the Wall II*
conjecture list, where it is defined as the square root of the sum of the
squares of the vertex degrees.
-/

namespace SimpleGraph

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The length of a graph on a finite vertex type: the square root of the sum, over all
vertices, of the squares of their degrees. -/
noncomputable def degreeL2Norm (G : SimpleGraph α) [DecidableRel G.Adj] : ℝ :=
  Real.sqrt (∑ v, (G.degree v : ℝ) ^ 2)

omit [DecidableEq α] in
/-- The length of a graph on a finite vertex type is nonnegative. -/
lemma degreeL2Norm_nonneg (G : SimpleGraph α) [DecidableRel G.Adj] :
    0 ≤ degreeL2Norm G :=
  Real.sqrt_nonneg _

end SimpleGraph
