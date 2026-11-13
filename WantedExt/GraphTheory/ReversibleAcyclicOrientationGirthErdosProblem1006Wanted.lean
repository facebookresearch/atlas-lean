/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

/-
# Acyclic orientations robust under one reversal (Erdős Problem 1006)

Erdős Problem 1006: let `G` be a graph of girth greater than `4`. Can the edges of `G` always be
directed so that there is no directed cycle, and reversing the direction of any one edge also
creates no directed cycle?
-/

module

public import Batteries.Util.ProofWanted
public import Mathlib.Combinatorics.SimpleGraph.Girth

@[expose] public section

namespace MathlibExt.GraphTheory.ReversibleAcyclicOrientationGirthErdosProblem1006Wanted

/-!
Source: T. F. Bloom, Erdős Problems, Problem #1006, https://www.erdosproblems.com/1006 (status
DISPROVED). UnsolvedMath record UM-30007120 (`EP-1006`), dataset ulamai/UnsolvedMath v1.8.0.

Graphs are finite (restricting the claim to finite graphs makes its refutation stronger). An
orientation is a relation directing each edge exactly one way; a directed cycle is a nonempty
directed walk from a vertex to itself (`Relation.TransGen`). Girth greater than `4` is `4 <
G.egirth`, which also holds for forests.
-/

/-- `o` is an orientation of `G`: it directs only edges of `G`, and each edge exactly one way. -/
def IsOrientation {V : Type*} (G : SimpleGraph V) (o : V → V → Prop) : Prop :=
  (∀ u v, o u v → G.Adj u v) ∧ ∀ u v, G.Adj u v → (o u v ↔ ¬ o v u)

/-- `o` has no directed cycle: no vertex reaches itself along a nonempty directed walk. -/
def IsAcyclicRel {V : Type*} (o : V → V → Prop) : Prop :=
  ∀ v, ¬ Relation.TransGen o v v

/-- The orientation obtained from `o` by reversing the arc `u → v`. -/
def reverseArc {V : Type*} (o : V → V → Prop) (u v : V) : V → V → Prop :=
  fun a b => (o a b ∧ ¬ (a = u ∧ b = v)) ∨ (a = v ∧ b = u)

/-- Erdős Problem 1006: every finite graph of girth greater than `4` has an acyclic orientation
that stays acyclic after reversing any single arc. -/
def girthFiveReversibleAcyclicOrientation : Prop :=
  ∀ (V : Type) [Fintype V] (G : SimpleGraph V), 4 < G.egirth →
    ∃ o : V → V → Prop, IsOrientation G o ∧ IsAcyclicRel o ∧
      ∀ u v, o u v → IsAcyclicRel (reverseArc o u v)

/--
Resolved false: Nešetřil and Rödl constructed, for every `g`, a finite graph of girth `g` in which
every orientation contains a directed cycle or a cycle that becomes directed after reversing one
arc; for an acyclic orientation, reversing that arc creates a directed cycle. erdosproblems.com/1006
lists the problem as disproved. Source: T. F. Bloom, Erdős Problems, Problem #1006,
https://www.erdosproblems.com/1006 (status DISPROVED); resolution: J. Nešetřil and V. Rödl, On a
probabilistic graph-theoretical method, Proc. Amer. Math. Soc. (1978), 417-421, for every g there is
a graph of girth g every orientation of which contains a directed cycle or a cycle obtained from a
directed cycle by reversing one arc (erdosproblems.com/1006), https://www.erdosproblems.com/1006.
-/
public theorem_wanted girthFiveReversibleAcyclicOrientation_refuted :
    ¬ girthFiveReversibleAcyclicOrientation

end MathlibExt.GraphTheory.ReversibleAcyclicOrientationGirthErdosProblem1006Wanted
