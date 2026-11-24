/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Edge-graceful labelings

This module defines edge-graceful labelings of finite simple graphs.

Reference: Lo's original definition as surveyed in https://arxiv.org/abs/2608.23881v1.

Main definitions:
* `SimpleGraph.incidentSum`: one-based incident-edge sum at a vertex.
* `SimpleGraph.inducedResidue`: induced vertex residue in `Fin (Fintype.card V)`.
* `SimpleGraph.IsEdgeGraceful`: existence of an edge bijection inducing a vertex bijection.
* `SimpleGraph.isEdgeGraceful_iff`: characterization via an explicit vertex bijection.
-/

@[expose] public section

open scoped BigOperators

namespace SimpleGraph

variable {V : Type*} [Fintype V]

/-- **Incident-edge sum.** Let $G$ be a simple graph on a finite vertex set $V$, let $q$ be a
natural number and let $\ell$ be a bijection from the edge set of $G$ to $\{0, 1, \dots, q-1\}$.
The incident-edge sum at a vertex $v$ is $\sum_{e \ni v} (\ell(e) + 1)$, the sum over the edges
$e$ of $G$ that contain $v$; in other words, the edges carry the labels $1, \dots, q$. -/
noncomputable def incidentSum (G : SimpleGraph V) (q : Nat)
    (label : G.edgeSet ≃ Fin q) (v : V) : Nat := by
  classical
  exact ∑ k : Fin q, if v ∈ (label.symm k).val then (k.val + 1) else 0

/-- **Induced vertex residue.** Let $G$ be a simple graph on a finite vertex set $V$, let $q$ be
a natural number and let $\ell$ be a bijection from the edge set of $G$ to $\{0, \dots, q-1\}$.
The induced residue of a vertex $v$ is the incident-edge sum at $v$ (with edge labels
$\ell(e) + 1$) reduced modulo $|V|$, viewed as an element of $\{0, \dots, |V| - 1\}$. When
$|V| = 0$ there are no vertices, so there is nothing to define. -/
noncomputable def inducedResidue (G : SimpleGraph V) (q : Nat)
    (label : G.edgeSet ≃ Fin q) (v : V) : Fin (Fintype.card V) := by
  classical
  by_cases hp : Fintype.card V = 0
  · exact Fin.elim0 (cast (congrArg Fin hp) ((Fintype.equivFin V) v))
  · exact ⟨G.incidentSum q label v % Fintype.card V,
      Nat.mod_lt _ (Nat.pos_of_ne_zero hp)⟩

/-- **Value of the induced residue.** Let $G$ be a simple graph on a finite nonempty vertex set
$V$, let $q$ be a natural number and let $\ell$ be a bijection from the edge set of $G$ to
$\{0, \dots, q-1\}$. For every vertex $v$, the induced residue of $v$ with respect to $\ell$, read
as a natural number, equals the incident-edge sum at $v$ with respect to $\ell$ modulo $|V|$. -/
theorem inducedResidue_val (G : SimpleGraph V) (q : Nat)
    (label : G.edgeSet ≃ Fin q) (v : V) (hp : Fintype.card V ≠ 0) :
    (G.inducedResidue q label v).val =
      G.incidentSum q label v % Fintype.card V := by
  classical
  unfold inducedResidue
  simp only [dite_eq_right hp]

/-- **Edge-graceful graph.** A simple graph $G$ on a finite vertex set $V$ is edge-graceful when
there are a natural number $q$ and a bijection $\ell$ from the edge set of $G$ to
$\{0, \dots, q-1\}$ such that the induced residue map, sending each vertex $v$ to the sum of
$\ell(e) + 1$ over the edges $e$ containing $v$ taken modulo $|V|$, is a bijection from $V$ to
$\{0, \dots, |V| - 1\}$. -/
def IsEdgeGraceful (G : SimpleGraph V) : Prop :=
  ∃ (q : Nat) (label : G.edgeSet ≃ Fin q),
    Function.Bijective (G.inducedResidue q label)

/-- **Edge-graceful graphs via a vertex bijection.** A simple graph $G$ on a finite vertex set $V$
is edge-graceful if and only if there are a natural number $q$, a bijection $\ell$ from the edge
set of $G$ to $\{0, \dots, q-1\}$ and a bijection $\lambda$ from $V$ to $\{0, \dots, |V| - 1\}$ such
that for every vertex $v$, $\lambda(v)$ is the induced residue of $v$ with respect to $\ell$ and,
if $V$ is nonempty, $\lambda(v)$ equals the incident-edge sum at $v$ with respect to $\ell$ modulo
$|V|$. -/
theorem isEdgeGraceful_iff (G : SimpleGraph V) :
    G.IsEdgeGraceful ↔
      ∃ (q : Nat) (eLabel : G.edgeSet ≃ Fin q)
        (vLabel : V ≃ Fin (Fintype.card V)),
        ∀ v, vLabel v = G.inducedResidue q eLabel v ∧
          (Fintype.card V ≠ 0 →
            (vLabel v).val = G.incidentSum q eLabel v % Fintype.card V) := by
  constructor
  · rintro ⟨q, eLabel, hbij⟩
    refine ⟨q, eLabel, Equiv.ofBijective _ hbij, fun v => ?_⟩
    constructor
    · rfl
    · intro hp
      exact G.inducedResidue_val q eLabel v hp
  · rintro ⟨q, eLabel, vLabel, h⟩
    refine ⟨q, eLabel, ?_⟩
    have h_eq : G.inducedResidue q eLabel = ⇑vLabel :=
      funext fun v => ((h v).1).symm
    rw [h_eq]
    exact vLabel.bijective

end SimpleGraph
