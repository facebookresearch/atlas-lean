/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.ZigZagExpanderFamily
public import MathlibExtTest.Combinatorics.RotationMap

@[expose] public section

open MathlibExt.Combinatorics MathlibExt.Combinatorics.RotationMap
open MathlibExtTest.Combinatorics.RotationMap

namespace MathlibExtTest.Combinatorics.ZigZagExpanderFamily

/-- Relabelling preserves the `(N, D, λ)` property: the `5`-cycle with its labels swapped. -/
example : (cycle5.relabel (Equiv.swap true false)).IsNDLambdaGraph 1 :=
  (isNDLambdaGraph_one cycle5).relabel _

/-- The single-vertex rotation map with one label, a `(1, 1, λ)`-graph for every `λ ≥ 0` (no
non-zero vector is orthogonal to the constants). It satisfies `|K| = |L|⁴`, so it is an admissible
seed of the zig-zag family; this instance is degenerate (`N = 1`), and a non-degenerate seed needs
an explicit `(D⁴, D, 1/5)`-graph, whose degree must be large: the elementary lower bound
`λ ≳ 1 / √D` forces `D ≳ 25`. -/
def trivialSeed : RotationMap Unit Unit where
  rot p := p
  rot_rot _ := rfl

example : trivialSeed.IsNDLambdaGraph (1 / 5) := by
  refine ⟨by norm_num, fun x hx => ?_⟩
  have : x = 0 := by funext u; simpa using hx
  subst this
  simp

/-- The family built from the trivial seed: every member is an `(N, 1, 2/5)`-graph. -/
example (t : ℕ) (e : (Unit × Unit) × (Unit × Unit) ≃ Unit) :
    (zigzagFamily trivialSeed e t).IsNDLambdaGraph (2 / 5) :=
  isNDLambdaGraph_zigzagFamily (by
    refine ⟨by norm_num, fun x hx => ?_⟩
    have : x = 0 := by funext u; simpa using hx
    subst this
    simp) e t

/-- The vertex count `|K|^(t + 1)` of the family for `K = Fin 3`. -/
example : Fintype.card (ZigZagFamilyVertex (Fin 3) 2) = 27 := by
  rw [card_zigzagFamilyVertex]; rfl

end MathlibExtTest.Combinatorics.ZigZagExpanderFamily
