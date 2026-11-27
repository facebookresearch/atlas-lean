/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.RotationMap

@[expose] public section

open MathlibExt.Combinatorics MathlibExt.Combinatorics.RotationMap

namespace MathlibExtTest.Combinatorics.RotationMap

/-- The `5`-cycle as a rotation map: label `false` steps forward and arrives with label `true`,
label `true` steps backward and arrives with label `false`. -/
def cycle5 : RotationMap (Fin 5) Bool where
  rot p := if p.2 then (p.1 - 1, false) else (p.1 + 1, true)
  rot_rot p := by
    obtain ⟨v, b⟩ := p
    cases b <;> simp

/-- The perfect matching on two vertices, a rotation map on `Bool` with one label. -/
def swap2 : RotationMap Bool Unit where
  rot p := (!p.1, ())
  rot_rot p := by simp

/-- Squaring follows two edges: from `0`, forward twice reaches `2`, arriving with labels
`(true, true)`. -/
example : cycle5.square.rot (0, (false, false)) = (2, (true, true)) := by decide

/-- The zig-zag product takes a step in the small graph, a step in the big graph, and a second
step in the small graph: from `(0, false)`, the small step moves to label `true`, the big step goes
backward to `4` and arrives with label `false`, and the second small step moves to `true`. -/
example : (cycle5.zigzag swap2).rot ((0, false), ((), ())) = ((4, true), ((), ())) := by decide

/-- Non-vacuity of the `(N, D, λ)` predicate on non-trivial multigraphs: the `5`-cycle, its square
and its zig-zag product with the perfect matching are `(N, D, 1)`-graphs, and squaring preserves
the predicate. -/
example : cycle5.IsNDLambdaGraph 1 := isNDLambdaGraph_one cycle5

example : cycle5.square.IsNDLambdaGraph (1 ^ 2) := (isNDLambdaGraph_one cycle5).square

example : (cycle5.zigzag swap2).IsNDLambdaGraph 1 := isNDLambdaGraph_one _

/-- The rows of the adjacency matrix of the `5`-cycle sum to `2`. -/
example : cycle5.adjMatrix.mulVec (1 : Fin 5 → ℝ) = (2 : ℝ) • (1 : Fin 5 → ℝ) := by
  simpa using adjMatrix_mulVec_one cycle5

end MathlibExtTest.Combinatorics.RotationMap
