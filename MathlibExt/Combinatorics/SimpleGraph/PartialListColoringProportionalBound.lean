/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import MathlibExt.Combinatorics.SimpleGraph.ListColoring
import MathlibExt.Combinatorics.SimpleGraph.PartialListColoring

/-!
# The partial list coloring proportional bound

Noel's fourteen-vertex graph refutes the Albertson–Grossman–Haas conjecture that lists of size
`t` on a graph of choice number `q` always allow a proportion of at least `t / q` of its
vertices to be colored.
-/

@[expose] public section

namespace MathlibExt.Combinatorics.PartialListColoringProportionalBoundWanted

/-- **Partial list colorability.** Let $G$ be a simple graph and assign to each vertex $v$ a finite
list $L(v)$ of colors. A finite set $S$ of vertices is partially list-colorable from $L$ when the
subgraph of $G$ induced by $S$ has a proper coloring $c$ with $c(v) \in L(v)$ for every
$v \in S$. No colors are assigned to vertices outside $S$. -/
def IsPartialListColoring {V C : Type*} [DecidableEq C]
    (G : SimpleGraph V) (lists : V → Finset C) (S : Finset V) : Prop :=
  ∃ color : S → C, (∀ v : S, color v ∈ lists (v : V)) ∧
    (∀ v w : S, G.Adj (v : V) (w : V) → color v ≠ color w)

/-- **Albertson–Grossman–Haas partial list coloring conjecture.** Let $G$ be a finite simple graph
on $n$ vertices whose choice number $q$ is positive, let $t \le q$ be a natural number, and assign
to each vertex $v$ a list $L(v)$ of exactly $t$ colors. Then there is a set $S$ of vertices of $G$
that is partially list-colorable from $L$ (the subgraph of $G$ induced by $S$ has a proper
coloring giving each vertex a color from its list) and satisfies $tn \le q|S|$, that is,
$|S| \ge tn/q$. -/
def conjecture : Prop :=
  ∀ (V : Type) [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : ℕ),
    0 < q → G.IsChoiceNumber q →
    ∀ (t : ℕ), t ≤ q →
    ∀ (C : Type) [DecidableEq C] (lists : V → Finset C),
    (∀ v, (lists v).card = t) →
    ∃ S : Finset V, IsPartialListColoring G lists S ∧ t * Fintype.card V ≤ q * S.card

open MathlibExt.GraphTheory.PartialListColoringWanted.Noel

/--
**The partial list coloring conjecture is false.** There exist a finite simple graph $G$ on
$n$ vertices whose choice number $q$ is positive, a natural number $t \le q$, and an assignment
to each vertex $v$ of a list $L(v)$ of exactly $t$ colors, such that every set $S$ of vertices
of $G$ whose induced subgraph has a proper coloring giving each vertex a color from its list
satisfies $q|S| < tn$.

Noel (arXiv:2609.23291, Sep 2026) gives a $14$-vertex graph with choice number $3$ and an
assignment of lists of exactly $2$ colors from which at most $9 < 28/3$ vertices can be properly
colored, so the conjectured bound $|S| \ge tn/q$ fails at $q = 3$, $t = 2$.

Source: Jonathan A. Noel, The Partial List Colouring Conjecture is False, arXiv preprint (2026),
arXiv:2609.23291, https://arxiv.org/abs/2609.23291. Moved from
`OpenConjectures/Combinatorics/PartialListColoringProportionalBound`.
-/
theorem conjecture_refuted : ¬ conjecture := by
  intro h
  obtain ⟨S, ⟨color, hmem, hproper⟩, hsize⟩ :=
    h V G 3 (by decide) isChoiceNumber_three 2 (by decide) ℕ L card_L
  -- The nine-vertex bound uses a total function whose values are tested only on S.
  let c (v : V) := if hv : v ∈ S then color ⟨v, hv⟩ else 0
  have h9 : S.card ≤ 9 := by
    apply card_le_nine (c := c)
    constructor
    · intro v hv
      simpa [c, hv] using hmem ⟨v, hv⟩
    · intro v hv w hw hadj
      simpa [c, hv, hw] using hproper ⟨v, hv⟩ ⟨w, hw⟩ hadj
  have h14 : Fintype.card V = 14 := by decide
  omega

end MathlibExt.Combinatorics.PartialListColoringProportionalBoundWanted
