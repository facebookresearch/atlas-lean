/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex

/-!
# List colorings of simple graphs

This file provides basic predicates for vertex list colorability and choice
numbers. A list coloring is represented by a Mathlib `SimpleGraph.Coloring`
whose value at each vertex belongs to that vertex's finite list of colors.
-/

@[expose] public section

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V} {q r : ℕ}

/-- **List colorability.** A simple graph $G$ is $q$-list-colorable if, for every set of colors and
every assignment of a finite list $L(v)$ of at least $q$ colors to each vertex $v$, there is a
proper coloring $c$ of $G$ with $c(v) \in L(v)$ for every vertex $v$. -/
def IsListColorable (G : SimpleGraph V) (q : ℕ) : Prop :=
  ∀ (C : Type) [DecidableEq C] (lists : V → Finset C),
    (∀ v, q ≤ (lists v).card) →
      ∃ color : G.Coloring C, ∀ v, color v ∈ lists v

/-- **Choice number.** A natural number $q$ is the choice number of a simple graph $G$ if $G$ is
$q$-list-colorable but is not $r$-list-colorable for any $r < q$. -/
def IsChoiceNumber (G : SimpleGraph V) (q : ℕ) : Prop :=
  G.IsListColorable q ∧ ∀ r < q, ¬G.IsListColorable r

/-- **Monotonicity of list colorability.** If a simple graph $G$ is $q$-list-colorable and
$q \le r$, then $G$ is $r$-list-colorable. -/
theorem IsListColorable.mono (hG : G.IsListColorable q) (hqr : q ≤ r) :
    G.IsListColorable r := by
  intro C _ lists hlists
  exact hG C lists fun v => hqr.trans (hlists v)

/-- **List-colorable graphs are colorable.** If a simple graph $G$ is $q$-list-colorable, then $G$
is $q$-colorable, that is, it has a proper coloring with $q$ colors. -/
theorem IsListColorable.colorable (hG : G.IsListColorable q) : G.Colorable q := by
  let lists : V → Finset (Fin q) := fun _ => Finset.univ
  obtain ⟨color, _⟩ := hG (Fin q) lists (by simp [lists])
  exact ⟨color⟩

end SimpleGraph

end
