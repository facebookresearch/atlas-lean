/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

import MathlibExt.Combinatorics.SimpleGraph.LongestCycle

namespace SimpleGraph.Walk

example {V : Type*} {G : SimpleGraph V} {v : V} (p : G.Walk v v) :
    p.IsLongestCycle ↔
      p.IsCycle ∧ ∀ (w : V) (q : G.Walk w w), q.IsCycle → q.length ≤ p.length :=
  Iff.rfl

example {V : Type*} {G : SimpleGraph V} {v : V} {p : G.Walk v v}
    (hp : p.IsLongestCycle) : p.IsCycle :=
  hp.1

-- A cycle has length at most the number of vertices.
example {V : Type*} [Fintype V] {G : SimpleGraph V} {v : V} {c : G.Walk v v}
    (hc : c.IsCycle) : c.length ≤ Fintype.card V :=
  hc.length_le_card

-- If a graph has a cycle, it has a longest cycle.
example {V : Type*} [Finite V] {G : SimpleGraph V} {x : V} (c₀ : G.Walk x x)
    (hc₀ : c₀.IsCycle) : ∃ (w : V) (c : G.Walk w w), c.IsLongestCycle :=
  exists_isLongestCycle c₀ hc₀

end SimpleGraph.Walk
