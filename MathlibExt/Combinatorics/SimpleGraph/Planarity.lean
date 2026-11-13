/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Set.Basic

/-!
# Straight-line planarity

A shared crossing-free straight-line drawing predicate for simple graphs.
-/

@[expose] public section

namespace SimpleGraph

/-- The closed straight-line segment from `a` to `b` in the real plane. -/
public def Segment (a b : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    p.1 = a.1 + t * (b.1 - a.1) ∧ p.2 = a.2 + t * (b.2 - a.2)}

/-- A crossing-free straight-line drawing of a simple graph. -/
public def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬Nonempty V ∨
    ∃ f : V → ℝ × ℝ, Function.Injective f ∧
      (∀ ⦃v w⦄, G.Adj v w → f v ≠ f w) ∧
      ∀ ⦃v w x y⦄, G.Adj v w → G.Adj x y →
        ({v, w} : Set V) ≠ {x, y} →
        Segment (f v) (f w) ∩ Segment (f x) (f y) ⊆
          ({f v, f w} : Set (ℝ × ℝ)) ∩ {f x, f y}

end SimpleGraph
