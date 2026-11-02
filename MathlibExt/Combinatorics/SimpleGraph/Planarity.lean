/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Data.Real.Basic
public import Mathlib.Data.Set.Basic

/-!
# Straight-line planarity

A shared crossing-free straight-line drawing predicate for simple graphs.
-/

@[expose] public section

namespace SimpleGraph

/-- **Closed segment in the plane.** For points $a$ and $b$ of $\mathbb{R}^2$, the closed segment
from $a$ to $b$ is the set of points $a + t(b - a)$ with $t \in \mathbb{R}$ and $0 \le t \le 1$. -/
public def Segment (a b : ℝ × ℝ) : Set (ℝ × ℝ) :=
  {p | ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧
    p.1 = a.1 + t * (b.1 - a.1) ∧ p.2 = a.2 + t * (b.2 - a.2)}

/-- **Straight-line planar graph.** A simple graph $G$ with vertex set $V$ is straight-line
planar if either $V$ is empty or there is an injective map $f$ from $V$ to $\mathbb{R}^2$
such that, for any two different edges $vw$ and $xy$ of $G$, the closed segment from $f(v)$
to $f(w)$ and the closed segment from $f(x)$ to $f(y)$ meet only in points of
$\{f(v), f(w)\} \cap \{f(x), f(y)\}$. -/
public def IsPlanar {V : Type*} (G : SimpleGraph V) : Prop :=
  ¬Nonempty V ∨
    ∃ f : V → ℝ × ℝ, Function.Injective f ∧
      (∀ ⦃v w⦄, G.Adj v w → f v ≠ f w) ∧
      ∀ ⦃v w x y⦄, G.Adj v w → G.Adj x y →
        ({v, w} : Set V) ≠ {x, y} →
        Segment (f v) (f w) ∩ Segment (f x) (f y) ⊆
          ({f v, f w} : Set (ℝ × ℝ)) ∩ {f x, f y}

end SimpleGraph
